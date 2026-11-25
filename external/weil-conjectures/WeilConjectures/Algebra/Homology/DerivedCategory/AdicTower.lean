/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Homology.DerivedCategory.MappingConeCoimage
public import WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit.Tower
public import Mathlib.Algebra.Homology.Linear

/-!
# Reductions of the homotopy limit of a normalized adic tower

Let `ϖ` be an element of a ring `R` acting on an abelian category `𝒜`. A *normalized
`ϖ`-adic tower* is a tower `T : ℕᵒᵖ ⥤ CochainComplex 𝒜 ℤ` such that `Tₘ` is killed by `ϖᵐ`
and is flat over `R/ϖᵐ` (multiplication by `ϖᵇ` on `T_{a+b}` has kernel `ϖᵃ T_{a+b}`), and
such that for `n ≤ m` the map `Tₘ / ϖⁿ ⟶ Tₙ` induced by the transition is a
quasi-isomorphism. These are the explicit models of the normalized systems
`Tₙ ≅ T_{n+1} ⊗ᴸ_{R/ϖⁿ⁺¹} R/ϖⁿ` of Bhatt–Scholze and of Stacks, Tag 09AW, with
`T_m / ϖⁿ ⟶ T_n` a quasi-isomorphism.

For each `n`, the tower `m ↦ cone(ϖⁿ : T_{m+n} ⟶ T_{m+n})` maps to the constant tower `Tₙ`
through the reductions `T_{m+n} ⟶ Tₙ`, and the fibre of this map is the tower
`m ↦ ker(ϖⁿ on T_{m+n})⟦1⟧`, whose transitions vanish after `n` steps by flatness. Hence the
derived limit of the cones is `Tₙ`: this is
`CochainComplex.IsNormalizedAdicTower.isIso_π_comp`.

## Main definitions

- `CochainComplex.IsNormalizedAdicTower`: normalized `ϖ`-adic towers of complexes.
- `CochainComplex.IsNormalizedAdicTower.cokerDesc`: the quasi-isomorphism
  `coker(ϖⁿ on T_{m+n}) ⟶ Tₙ`.
- `CochainComplex.IsNormalizedAdicTower.cokerIso`: the induced isomorphism
  `coker(ϖⁿ on T_{m+n}) ≅ Tₙ` in the derived category.

## Main results

- `CochainComplex.IsNormalizedAdicTower.isIso_π_comp`: for a homotopy limit `c` of the tower of
  cones `m ↦ cone(ϖⁿ on T_{m+n})` in the derived category, the map `c.pt ⟶ Tₙ` induced by the
  reductions is an isomorphism.

-/

@[expose] public section

universe v u

open CategoryTheory Category Limits Opposite Pretriangulated

namespace CochainComplex

variable {R : Type*} [Ring R] {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] [Linear R 𝒜]

/-- The functor sending a complex `X` to the arrow `r • 𝟙 X`. -/
@[simps]
noncomputable abbrev smulArrow (r : R) : CochainComplex 𝒜 ℤ ⥤ Arrow (CochainComplex 𝒜 ℤ) where
  obj X := Arrow.mk (r • 𝟙 X)
  map f := Arrow.homMk f f (by simp)

/-- A tower `T` of cochain complexes is a *normalized `ϖ`-adic tower* if `Tₙ` is killed by `ϖⁿ`,
if for `n ≤ m` the map `coker(ϖⁿ on Tₘ) ⟶ Tₙ` induced by the transition is a
quasi-isomorphism, and if `T_{a+b}` is flat over `R/ϖ^{a+b}` in the sense that the kernel of
`ϖᵇ` is the image of `ϖᵃ`. -/
structure IsNormalizedAdicTower (ϖ : R) (T : ℕᵒᵖ ⥤ CochainComplex 𝒜 ℤ) : Prop where
  smul_eq_zero (n : ℕ) : ϖ ^ n • 𝟙 (T.obj (op n)) = 0
  quasiIso_cokernelDesc {n m : ℕ} (h : n ≤ m) :
    QuasiIso (cokernel.desc (ϖ ^ n • 𝟙 (T.obj (op m))) (T.map (homOfLE h).op) (by
      rw [Linear.smul_comp, id_comp, ← comp_id (T.map (homOfLE h).op), ← Linear.comp_smul,
        smul_eq_zero n, comp_zero]))
  exact_smul (a b : ℕ) :
    (ShortComplex.mk (ϖ ^ a • 𝟙 (T.obj (op (a + b)))) (ϖ ^ b • 𝟙 (T.obj (op (a + b)))) (by
      rw [Linear.smul_comp, id_comp, smul_smul, ← pow_add, add_comm, smul_eq_zero])).Exact

namespace IsNormalizedAdicTower

open ConeCoimage

variable {ϖ : R} {T : ℕᵒᵖ ⥤ CochainComplex 𝒜 ℤ} (hT : IsNormalizedAdicTower ϖ T) (n : ℕ)

/-- The tower of arrows `m ↦ (ϖⁿ : T_{m+n} ⟶ T_{m+n})`. -/
noncomputable abbrev arrowTower : ℕᵒᵖ ⥤ Arrow (CochainComplex 𝒜 ℤ) :=
  addOpFunctor n ⋙ T ⋙ smulArrow (ϖ ^ n)

omit [Linear R 𝒜] in
/-- The reductions `T_{m+n} ⟶ Tₙ`. -/
@[simps]
def red : addOpFunctor n ⋙ T ⟶ (Functor.const ℕᵒᵖ).obj (T.obj (op n)) where
  app m := T.map (homOfLE (Nat.le_add_left n m.unop)).op
  naturality {m m'} f := by
    dsimp
    rw [comp_id, ← Functor.map_comp]
    rfl

include hT in
lemma smul_comp_red (m : ℕᵒᵖ) :
    ((arrowTower (ϖ := ϖ) (T := T) n).obj m).hom ≫ (red n).app m = 0 := by
  dsimp
  rw [Linear.smul_comp, id_comp,
    show ϖ ^ n • (red n).app m = (red n).app m ≫ (ϖ ^ n • 𝟙 (T.obj (op n))) by simp,
    hT.smul_eq_zero, comp_zero]

/-- The quasi-isomorphism `coker(ϖⁿ on T_{m+n}) ⟶ Tₙ` induced by the reduction. -/
noncomputable def cokerDesc (m : ℕᵒᵖ) :
    coker.obj ((arrowTower (ϖ := ϖ) (T := T) n).obj m) ⟶ T.obj (op n) :=
  cokernel.desc _ ((red n).app m) (hT.smul_comp_red n m)

/-- The map `coker(ϖⁿ on T_{m+n}) ⟶ Tₙ` induced by the reduction is a quasi-isomorphism. -/
lemma quasiIso_cokerDesc (m : ℕᵒᵖ) : QuasiIso (hT.cokerDesc n m) :=
  hT.quasiIso_cokernelDesc (Nat.le_add_left n m.unop)

@[reassoc (attr := simp)]
lemma π_cokerDesc (m : ℕᵒᵖ) :
    cokernel.π (ϖ ^ n • 𝟙 (T.obj ((addOpFunctor n).obj m))) ≫ hT.cokerDesc n m =
      (red n).app m :=
  cokernel.π_desc _ _ _

@[reassoc (attr := simp)]
lemma coker_map_cokerDesc {m m' : ℕᵒᵖ} (f : m ⟶ m') :
    coker.map ((arrowTower (ϖ := ϖ) (T := T) n).map f) ≫ hT.cokerDesc n m' =
      hT.cokerDesc n m := by
  apply coequalizer.hom_ext
  dsimp
  simp only [cokernel.π_desc_assoc, assoc, π_cokerDesc]
  simpa using (red n).naturality f

section DerivedCategory

variable [HasDerivedCategory 𝒜]

/-- The isomorphism `coker(ϖⁿ on T_{m+n}) ≅ Tₙ` in the derived category, induced by the
quasi-isomorphism `cokerDesc`. -/
noncomputable def cokerIso (m : ℕᵒᵖ) :
    DerivedCategory.Q.obj (coker.obj ((arrowTower (ϖ := ϖ) (T := T) n).obj m)) ≅
      DerivedCategory.Q.obj (T.obj (op n)) :=
  have := hT.quasiIso_cokerDesc n m
  asIso (DerivedCategory.Q.map (hT.cokerDesc n m))

@[simp]
lemma cokerIso_hom (m : ℕᵒᵖ) :
    (hT.cokerIso n m).hom = DerivedCategory.Q.map (hT.cokerDesc n m) :=
  rfl

@[reassoc (attr := simp)]
lemma Q_map_cokerDesc_cokerIso_inv (m : ℕᵒᵖ) :
    DerivedCategory.Q.map (hT.cokerDesc n m) ≫ (hT.cokerIso n m).inv = 𝟙 _ :=
  (hT.cokerIso n m).hom_inv_id

@[reassoc (attr := simp)]
lemma cokerIso_inv_coker_map {m m' : ℕᵒᵖ} (f : m ⟶ m') :
    (hT.cokerIso n m).inv ≫
        DerivedCategory.Q.map (coker.map ((arrowTower (ϖ := ϖ) (T := T) n).map f)) =
      (hT.cokerIso n m').inv := by
  rw [Iso.inv_comp_eq, Iso.eq_comp_inv, cokerIso_hom, cokerIso_hom, ← Functor.map_comp,
    hT.coker_map_cokerDesc n f]

end DerivedCategory

include hT in
/-- The kernel of `ϖⁿ` on `T_{m+N+n}` is killed by the transition to `T_{m+n}` when `n ≤ N`. -/
lemma kernel_ι_comp_map_eq_zero (m N : ℕ) (hN : n ≤ N) :
    kernel.ι (ϖ ^ n • 𝟙 (T.obj (op (m + N + n)))) ≫
      T.map (homOfLE (by omega : m + n ≤ m + N + n)).op = 0 := by
  let S := ShortComplex.mk (ϖ ^ (m + N) • 𝟙 (T.obj (op (m + N + n))))
    (ϖ ^ n • 𝟙 (T.obj (op (m + N + n)))) (by
      rw [Linear.smul_comp, id_comp, smul_smul, ← pow_add, add_comm, hT.smul_eq_zero])
  have hS : S.Exact := hT.exact_smul (m + N) n
  have := (S.exact_iff_epi_kernel_lift).1 hS
  rw [← cancel_epi (kernel.lift S.g S.f S.zero), comp_zero, kernel.lift_ι_assoc]
  change (ϖ ^ (m + N) • 𝟙 _) ≫ _ = 0
  rw [Linear.smul_comp, id_comp, ← comp_id (T.map _), ← Linear.comp_smul]
  rw [show ϖ ^ (m + N) = ϖ ^ (N - n) * ϖ ^ (m + n) by rw [← pow_add]; congr 1; omega,
    ← smul_smul, hT.smul_eq_zero, smul_zero, comp_zero]

include hT in
/-- Multiplication by `ϖᵃ` followed by multiplication by `ϖᵇ` vanishes on `Tₘ` for
`a + b = m`. -/
lemma smul_comp_smul_eq_zero {a b m : ℕ} (h : a + b = m) :
    (ϖ ^ a • 𝟙 (T.obj (op m))) ≫ (ϖ ^ b • 𝟙 (T.obj (op m))) = 0 := by
  subst h
  rw [Linear.smul_comp, id_comp, smul_smul, ← pow_add, add_comm, hT.smul_eq_zero]

include hT in
/-- Multiplication by `ϖᵃ` followed by multiplication by `ϖᵇ` on `Tₘ` is exact for
`a + b = m`. -/
lemma exact_smul_of_add_eq {a b m : ℕ} (h : a + b = m) :
    (ShortComplex.mk _ _ (hT.smul_comp_smul_eq_zero h)).Exact := by
  subst h
  exact hT.exact_smul a b

include hT in
/-- If `T₁` is exact in degree `i + 1`, the transition `T_{n+1} ⟶ Tₙ` is an epimorphism on
`Hⁱ`: it factors as `T_{n+1} ⟶ coker(ϖⁿ) ⟶ Tₙ`, the second map being a quasi-isomorphism, and
the kernel `ϖⁿ T_{n+1} ≅ coker(ϖ on T_{n+1})` of the first one is quasi-isomorphic to `T₁`
(right exactness in the top degree). -/
lemma epi_homologyMap_map (i : ℤ) (h₁ : (T.obj (op 1)).ExactAt (i + 1)) (n : ℕ) :
    Epi (HomologicalComplex.homologyMap (T.map (homOfLE n.le_succ).op) i) := by
  let X := T.obj (op (n + 1))
  have hex := hT.exact_smul_of_add_eq (add_comm 1 n)
  let S := ShortComplex.mk (cokernel.desc (ϖ ^ 1 • 𝟙 X) (ϖ ^ n • 𝟙 X)
    (hT.smul_comp_smul_eq_zero (add_comm 1 n)))
    (cokernel.π (ϖ ^ n • 𝟙 X)) (coequalizer.hom_ext (by simp))
  let φ : ShortComplex.mk (ϖ ^ n • 𝟙 X) (cokernel.π (ϖ ^ n • 𝟙 X)) (cokernel.condition _) ⟶
      S :=
    { τ₁ := cokernel.π (ϖ ^ 1 • 𝟙 X)
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _ }
  have hS : S.ShortExact :=
    { exact := (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).1
        (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _))
      mono_f := (ShortComplex.exact_iff_mono_cokernel_desc _).1 hex }
  have := hT.quasiIso_cokernelDesc (Nat.le_add_left 1 n)
  have hδ : hS.δ i (i + 1) rfl = 0 := (IsZero.of_iso (h₁.isZero_homology)
    (asIso (HomologicalComplex.homologyMap (cokernel.desc (ϖ ^ 1 • 𝟙 X)
      (T.map (homOfLE (Nat.le_add_left 1 n)).op) _) (i + 1)))).eq_of_tgt _ _
  have hepi := (hS.homology_exact₃ i (i + 1) rfl).epi_f hδ
  have := hT.quasiIso_cokernelDesc n.le_succ
  rw [← cokernel.π_desc (ϖ ^ n • 𝟙 X) (T.map (homOfLE n.le_succ).op) (by
    rw [Linear.smul_comp, id_comp, ← comp_id (T.map _), ← Linear.comp_smul,
      hT.smul_eq_zero, comp_zero]), HomologicalComplex.homologyMap_comp]
  exact epi_comp' hepi inferInstance

variable [HasDerivedCategory 𝒜]

variable [HasLimitsOfShape (Discrete ℕ) (DerivedCategory 𝒜)]

/-- For a homotopy limit `c` of the tower `m ↦ cone(ϖⁿ on T_{m+n})` in the derived category, the
map `c.pt ⟶ Tₙ` induced by the reductions `cone(ϖⁿ on T_{m+n}) ⟶ Tₙ` is an isomorphism: the
fibres of these maps form a tower whose transitions vanish after `n` steps. -/
theorem isIso_π_comp {c : Cone (arrowTower (ϖ := ϖ) (T := T) n ⋙ cone ⋙ DerivedCategory.Q)}
    (hc : IsHomotopyLimit c) :
    IsIso (c.π.app (op 0) ≫ DerivedCategory.Q.map
      (ρ.app _ ≫ desc.app _ ≫ hT.cokerDesc n (op 0))) := by
  let A := arrowTower (ϖ := ϖ) (T := T) n
  let Q := DerivedCategory.Q (C := 𝒜)
  let ι : A ⋙ ker ⋙ Q ⟶ A ⋙ cone ⋙ Q :=
    Functor.whiskerLeft _ (Functor.whiskerRight kerι Q)
  let β : A ⋙ cone ⋙ Q ⟶ (Functor.const ℕᵒᵖ).obj (Q.obj (T.obj (op n))) :=
    { app m := Q.map (ρ.app _ ≫ desc.app _ ≫ hT.cokerDesc n m)
      naturality {m m'} f := by
        change Q.map (cone.map (A.map f)) ≫ _ = _ ≫ 𝟙 _
        rw [comp_id, ← Functor.map_comp]
        congr 1
        rw [reassoc_of% (ρ.naturality (A.map f)), reassoc_of% (desc.naturality (A.map f)),
          hT.coker_map_cokerDesc] }
  let δ : (Functor.const ℕᵒᵖ).obj (Q.obj (T.obj (op n))) ⟶
      (A ⋙ ker ⋙ Q) ⋙ CategoryTheory.shiftFunctor (DerivedCategory 𝒜) (1 : ℤ) :=
    { app m := (hT.cokerIso n m).inv ≫ (triangle (A.obj m)).mor₃
      naturality {m m'} f := by
        change 𝟙 _ ≫ _ = _ ≫ (Q.map (ker.map (A.map f)))⟦(1 : ℤ)⟧'
        rw [id_comp, assoc, triangle_mor₃_naturality, ← assoc, hT.cokerIso_inv_coker_map] }
  refine IsHomotopyLimit.isIso_π_comp_of_triangles ι β δ (fun m ↦ ?_) n (fun m ↦ ?_) hc
  · refine isomorphic_distinguished _ (triangle_distinguished (A.obj (op m))) _
      (Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (hT.cokerIso n (op m)).symm
        ?_ ?_ ?_)
    · simp [ι, triangle, Q]
    · dsimp only [β, triangle, Triangle.mk_mor₂, Iso.symm_hom, Iso.refl_hom]
      exact (congrArg (· ≫ _) ((Q.congr_map (assoc _ _ _).symm).trans (Q.map_comp _ _))).trans
        ((assoc _ _ _).trans ((congrArg _ (hT.Q_map_cokerDesc_cokerIso_inv n _)).trans
          ((comp_id _).trans (id_comp _).symm)))
    · simp [δ]
  · change Q.map (ker.map (A.map _)) = 0
    rw [ker_map_eq_zero _ (hT.kernel_ι_comp_map_eq_zero n m n le_rfl), Functor.map_zero]

end IsNormalizedAdicTower

end CochainComplex
