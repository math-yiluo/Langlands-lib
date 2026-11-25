/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.DerivedBaseChange
public import WeilConjectures.Algebra.Homology.DerivedCategory.ProjectiveHom
public import WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit
public import WeilConjectures.Algebra.Homology.MatrixComplexTower
public import WeilConjectures.Algebra.Homology.MinimalComplex
public import WeilConjectures.Algebra.Homology.MinimalMatrixComplex
public import WeilConjectures.CategoryTheory.DerivedCategory.Perfect
public import WeilConjectures.CategoryTheory.DerivedCategory.PerfectTrace
public import WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit.Tower

/-!
# Normalized towers of perfect complexes over an adic ring

Let `R` be a commutative ring with a tower of quotients `π n : R →+* A n` and transitions
`ρ n : A (n + 1) →+* A n` (the intended case is `R = 𝒪_E` and `A n = 𝒪_E ⧸ ϖⁿ⁺¹`). A
*normalized tower of perfect complexes* (`ModuleCat.NormalizedPerfectTower`) is a family of
perfect complexes `Q n ∈ D(A n)` with maps `Q (n + 1) ⟶ Res Q n` exhibiting `Q n` as the
derived base change `Q (n + 1) ⊗ᴸ_{A (n + 1)} A n`. Its restrictions of scalars form a tower
`n ↦ Res Q n` in `D(R)`.

When the `A n` are local and `R` is complete and separated for the tower, the derived limit
`P = R lim_n Q n` of this tower is represented by a bounded complex of finite free
`R`-modules and reduces to the levels, `P ⊗ᴸ_R A n ≅ Q n` (Stacks, Tag 09AW). A compatible
family of endomorphisms `f n` of the `Q n` lifts to an endomorphism `V` of `P`, and the
categorical trace of any lift reduces to the traces of the `f n`.

## Main definitions

- `ModuleCat.NormalizedPerfectTower`: a normalized tower of perfect complexes.
- `ModuleCat.NormalizedPerfectTower.restrict`: the tower `n ↦ Res Q n` in `D(R)`.
- `ModuleCat.NormalizedPerfectTower.IsCompatible`: compatible families of endomorphisms.
- `ModuleCat.NormalizedPerfectTower.IsLift`: lifts of a compatible family to the derived limit.

## Main results

- `ModuleCat.NormalizedPerfectTower.exists_iso_Q_obj_of_isHomotopyLimit`: the derived limit is
  represented by a bounded complex of finite free `R`-modules.
- `ModuleCat.NormalizedPerfectTower.isDerivedBaseChange_π_app`: the legs `P ⟶ Res Q n` of the
  derived limit exhibit `Q n` as `P ⊗ᴸ_R A n`.
- `ModuleCat.NormalizedPerfectTower.exists_isLift`: compatible families lift.
- `ModuleCat.NormalizedPerfectTower.exists_trace_eq_of_isLift`,
  `ModuleCat.NormalizedPerfectTower.trace_eq_of_isLift`: the trace of a lift reduces to the
  traces of the family, and does not depend on the lift.

## Implementation notes

Derived base change is expressed by universal arrows (`ModuleCat.IsDerivedBaseChange`): the
leg `pr_n : P ⟶ Res Q n` is the blueprint's `π_n : P ⊗ᴸ A n ⟶ Q n` read through the adjunction
between derived base change and restriction of scalars. For the same reason the blueprint's
condition `π_n ∘ (V ⊗ᴸ A n) = f n ∘ π_n` on a lift `V` is the condition
`V ≫ pr_n = pr_n ≫ Res (f n)` of `ModuleCat.NormalizedPerfectTower.IsLift`: `V ⊗ᴸ A n` is the
unique endomorphism `g` of `P ⊗ᴸ A n` with `pr_n ≫ Res g = V ≫ pr_n`.

The proof follows the blueprint. Each `Q n` has a minimal model, a bounded complex of finite
free `A n`-modules whose differentials vanish modulo the maximal ideal
(`CochainComplex.exists_homotopyEquiv_isMinimal`); quasi-isomorphisms between minimal models are
isomorphisms (`CochainComplex.isIso_of_quasiIso_of_isMinimal`). In bases, the models are given by
matrices, and lifting invertible matrices along `A (n + 1) ⟶ A n` strictifies the tower into a
tower of matrix complexes whose transitions are the reductions of the entries. Their entrywise
limit is the bounded free complex over `R` representing `P`
(`DerivedCategory.isHomotopyLimit_mapCone_Q_of_epi`). Lifts are built by choosing chain-level
representatives level by level and correcting them by lifted homotopies, and traces are
alternating sums of matrix traces
(`DerivedCategory.trace_eq_algebraMap_sum_negOnePow_linearMapTrace`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite Pretriangulated MonoidalCategory

namespace ModuleCat

variable {R : Type u} [CommRing R] {A : ℕ → Type u} [∀ n, CommRing (A n)]
  [HasDerivedCategory.{u} (ModuleCat.{u} R)] [∀ n, HasDerivedCategory.{u} (ModuleCat.{u} (A n))]
  {π : ∀ n, R →+* A n} {ρ : ∀ n, A (n + 1) →+* A n}

variable (π ρ) in
/-- A *normalized tower of perfect complexes* over the tower of rings `A n` (with `π n : R →+* A n`
and transitions `ρ n : A (n + 1) →+* A n`, `ρ n ∘ π (n + 1) = π n`) is a family of perfect complexes
`Q n ∈ D(A n)` together with maps `Q (n + 1) ⟶ Res Q n` exhibiting `Q n` as the derived base change
`Q (n + 1) ⊗ᴸ_{A (n + 1)} A n`. -/
structure NormalizedPerfectTower (hρ : ∀ n, π n = (ρ n).comp (π (n + 1))) where
  /-- The level `Q n ∈ D(A n)`. -/
  obj (n : ℕ) : DerivedCategory (ModuleCat.{u} (A n))
  /-- Each level is perfect. -/
  isPerfect (n : ℕ) : (obj n).IsPerfect
  /-- The transition `Q (n + 1) ⟶ Res Q n`. -/
  map (n : ℕ) : obj (n + 1) ⟶ (derivedRestrictScalars (ρ n)).obj (obj n)
  /-- The transition exhibits `Q n` as `Q (n + 1) ⊗ᴸ_{A (n + 1)} A n`. -/
  isDerivedBaseChange (n : ℕ) : IsDerivedBaseChange (map n)

namespace NormalizedPerfectTower

variable {hρ : ∀ n, π n = (ρ n).comp (π (n + 1))} (T : NormalizedPerfectTower π ρ hρ)

/-- The tower `n ↦ Res Q n` in `D(R)` of the restrictions of scalars of the levels, with the
restricted transitions. -/
noncomputable def restrict : ℕᵒᵖ ⥤ DerivedCategory (ModuleCat.{u} R) :=
  Functor.ofOpSequence (X := fun n ↦ (derivedRestrictScalars (π n)).obj (T.obj n)) fun n ↦
    (derivedRestrictScalars (π (n + 1))).map (T.map n) ≫
      (derivedRestrictScalarsCompIso (hρ n)).hom.app (T.obj n)

@[simp]
lemma restrict_obj (n : ℕ) :
    T.restrict.obj (op n) = (derivedRestrictScalars (π n)).obj (T.obj n) :=
  rfl

lemma restrict_map_succ (n : ℕ) :
    T.restrict.map (homOfLE n.le_succ).op =
      (derivedRestrictScalars (π (n + 1))).map (T.map n) ≫
        (derivedRestrictScalarsCompIso (hρ n)).hom.app (T.obj n) :=
  Functor.ofOpSequence_map_homOfLE_succ _ n

/-- A family of endomorphisms `f n` of the levels is *compatible* if `f n` is the base change
of `f (n + 1)`: `f (n + 1)` followed by the transition is the transition followed by `f n`. -/
def IsCompatible (f : ∀ n, T.obj n ⟶ T.obj n) : Prop :=
  ∀ n, T.map n ≫ (derivedRestrictScalars (ρ n)).map (f n) = f (n + 1) ≫ T.map n

/-- An endomorphism `V` of the point of a cone `c` over `T.restrict` is a *lift* of a family
`f n` of endomorphisms of the levels if `V ≫ pr_n = pr_n ≫ Res (f n)` for the legs
`pr_n : c.pt ⟶ Res Q n`. When the legs exhibit `Q n` as `c.pt ⊗ᴸ_R A n`
(`ModuleCat.NormalizedPerfectTower.isDerivedBaseChange_π_app`), this says that `f n` is
`V ⊗ᴸ_R A n` read through `pr_n`. -/
def IsLift (c : Cone T.restrict) (f : ∀ n, T.obj n ⟶ T.obj n) (V : c.pt ⟶ c.pt) : Prop :=
  ∀ n, V ≫ c.π.app (op n) = c.π.app (op n) ≫ (derivedRestrictScalars (π n)).map (f n)

variable [∀ n, IsLocalRing (A n)] (hπ : ∀ n, Function.Surjective (π n)) {ϖ : R}
  (hker : ∀ n, RingHom.ker (π n) = Ideal.span {ϖ ^ (n + 1)})
  (hcomplete : ∀ x : ∀ n, A n, (∀ n, ρ n (x (n + 1)) = x n) → ∃ r : R, ∀ n, π n r = x n)
  (hsep : ∀ r : R, (∀ n, π n r = 0) → r = 0)
  {c : Cone T.restrict} (hc : IsHomotopyLimit c)

/-! ### Strictification of the tower by minimal matrix complexes -/

/-- A minimal matrix model of the level `n` of a normalized tower: a minimal matrix complex `M`
of ranks `r` over `A n` together with an isomorphism `Q M ≅ Q n`. -/
structure LevelModel (r : ℤ → ℕ) (n : ℕ) where
  /-- The minimal matrix complex. -/
  M : MatrixComplex r (A n)
  /-- The matrix complex is minimal. -/
  isMinimal : M.IsMinimal
  /-- The identification of the image of `M` with the level `Q n`. -/
  iso : DerivedCategory.Q.obj M.complex ≅ T.obj n

variable {T} in
/-- The compatibility of level models at `n + 1` and `n` with the transition `T.map n`: the
matrices of the first reduce to those of the second, and the reduction corresponds to the
transition. -/
def LevelModel.IsSucc {r : ℤ → ℕ} {n : ℕ} (x : T.LevelModel r n) (y : T.LevelModel r (n + 1)) :
    Prop :=
  ∃ h : ∀ i, (y.M.d i).map (ρ n) = x.M.d i,
    DerivedCategory.Q.map (y.M.reduction (ρ n) x.M h) ≫
      (ModuleCat.restrictScalars.{u} (ρ n)).mapDerivedCategoryFactors.inv.app x.M.complex ≫
        (derivedRestrictScalars (ρ n)).map x.iso.hom = y.iso.hom ≫ T.map n

variable {T} in
omit [HasDerivedCategory.{u} (ModuleCat.{u} R)] in
include hπ hker in
/-- Every level model at `n` extends to a compatible level model at `n + 1`: take a minimal
model of `Q (n + 1)`, compare its reduction with the model at `n` (minimality makes the
comparison an isomorphism of complexes, given by invertible matrices), lift these matrices to
`A (n + 1)` and conjugate. -/
lemma LevelModel.exists_isSucc {r : ℤ → ℕ} {hi : ℤ} (hhi : ∀ i, hi < i → r i = 0) {n : ℕ}
    (x : T.LevelModel r n) : ∃ y : T.LevelModel r (n + 1), x.IsSucc y := by
  obtain ⟨r', lo', hi', M', hlo', hhi', hM', ⟨e'⟩⟩ :=
    MatrixComplex.exists_iso_Q_obj_of_isPerfect (T.isPerfect (n + 1))
  have hρs : Function.Surjective (ρ n) := Function.Surjective.of_comp (g := π (n + 1)) (by
    rw [← RingHom.coe_comp, ← hρ n]
    exact hπ n)
  have := IsLocalHom.of_surjective (ρ n) hρs
  have hη := M'.isDerivedBaseChange_reduction (ρ n) hρs
    (RingHom.ker_eq_span_singleton_of_comp (hπ (n + 1)) (ρ n) ((hρ n) ▸ hker n)) lo' hi' hlo'
    hhi' (M'.map (ρ n)) fun _ ↦ rfl
  obtain ⟨θ, hθ⟩ := (hη (T.obj n)).2 (e'.hom ≫ T.map n)
  have : IsIso θ := hη.isIso (IsDerivedBaseChange.of_iso e' (T.isDerivedBaseChange n)) θ hθ
  obtain ⟨g, hg, hgθ⟩ := MatrixComplex.exists_isIso_Q_map_eq (hM'.map (ρ n)) x.isMinimal hi' hi
    hhi' hhi (θ ≫ x.iso.inv)
  obtain rfl : r' = r := funext (MatrixComplex.rank_eq_of_isIso g)
  choose b hb hbu using fun i ↦ MatrixComplex.exists_map_eq_isUnit_det (ρ n) hρs
    (MatrixComplex.toMatrix g i) (MatrixComplex.isUnit_det_toMatrix g i)
  refine ⟨⟨M'.conj b hbu, hM'.conj b hbu,
    (asIso (DerivedCategory.Q.map (M'.conjHom b hbu))).symm ≪≫ e'⟩,
    M'.map_conj_d b hbu (ρ n) x.M _ hb (MatrixComplex.toMatrix_comm g), ?_⟩
  rw [← cancel_epi (DerivedCategory.Q.map (M'.conjHom b hbu))]
  simp only [Iso.trans_hom, Iso.symm_hom, asIso_inv, Category.assoc, IsIso.hom_inv_id_assoc]
  rw [← hθ, ← Functor.map_comp_assoc, MatrixComplex.reduction_naturality (ρ n) (fun _ ↦ rfl) _
    _ g fun i ↦ by rw [MatrixComplex.toMatrix_conjHom, hb], Functor.map_comp_assoc,
    Functor.mapDerivedCategoryFactors_inv_naturality_assoc, ← Functor.map_comp, hgθ,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]
  simp only [Category.assoc]

variable {T} in
include hπ hker in
/-- A choice of a compatible level model at `n + 1` extending a level model at `n`. -/
noncomputable def LevelModel.succ {r : ℤ → ℕ} {hi : ℤ} (hhi : ∀ i, hi < i → r i = 0) {n : ℕ}
    (x : T.LevelModel r n) : T.LevelModel r (n + 1) :=
  (LevelModel.exists_isSucc hπ hker hhi x).choose

omit [HasDerivedCategory.{u} (ModuleCat.{u} R)] in
variable {T} in
/-- The level model `LevelModel.succ` is compatible with the level model it extends. -/
lemma LevelModel.isSucc_succ {r : ℤ → ℕ} {hi : ℤ} (hhi : ∀ i, hi < i → r i = 0) {n : ℕ}
    (x : T.LevelModel r n) : x.IsSucc (x.succ hπ hker hhi) :=
  (LevelModel.exists_isSucc hπ hker hhi x).choose_spec

variable {T} in
/-- The compatible sequence of level models starting from a level model at `0`. -/
noncomputable def levelModelSeq {r : ℤ → ℕ} {hi : ℤ} (hhi : ∀ i, hi < i → r i = 0)
    (x₀ : T.LevelModel r 0) : ∀ n, T.LevelModel r n
  | 0 => x₀
  | n + 1 => (levelModelSeq hhi x₀ n).succ hπ hker hhi

variable {T} in
/-- The isomorphism between the tower `n ↦ Res (M n)` of a compatible sequence of level models
and the tower `T.restrict`, in the derived category. -/
noncomputable def towerHom {r : ℤ → ℕ} (level : ∀ n, T.LevelModel r n)
    (hs : ∀ n, (level n).IsSucc (level (n + 1))) :
    MatrixComplex.towerFunctor hρ (fun n ↦ (level n).M) (fun n ↦ (hs n).1) ⋙
      DerivedCategory.Q ⟶ T.restrict :=
  NatTrans.ofOpSequence (fun n ↦
    (ModuleCat.restrictScalars.{u} (π n)).mapDerivedCategoryFactors.inv.app (level n).M.complex ≫
      (derivedRestrictScalars (π n)).map (level n).iso.hom) fun n ↦ by
    have hnat := (derivedRestrictScalarsCompIso (hρ n)).hom.naturality (level n).iso.hom
    simp only [Functor.comp_obj, Functor.comp_map] at hnat
    rw [Functor.comp_map, MatrixComplex.towerFunctor_map_succ, restrict_map_succ,
      ← Category.assoc, ModuleCat.Q_map_restrictScalars_comp]
    simp only [Category.assoc]
    rw [← hnat, ← Functor.map_comp_assoc, Category.assoc, (hs n).2,
      Functor.map_comp_assoc]

variable {T} in
/-- The comparison `NormalizedPerfectTower.towerHom` is an isomorphism. -/
instance {r : ℤ → ℕ} (level : ∀ n, T.LevelModel r n)
    (hs : ∀ n, (level n).IsSucc (level (n + 1))) : IsIso (towerHom level hs) := by
  have (X : ℕᵒᵖ) : IsIso ((towerHom level hs).app X) := by
    rw [towerHom, NatTrans.ofOpSequence_app]
    infer_instance
  exact NatIso.isIso_of_isIso_app _

variable (c) in
/-- A *matrix model* of a normalized tower `T` and of a cone `c` over `T.restrict`: a compatible
sequence of minimal matrix models of the levels, with bounded ranks, and a matrix complex `L`
over `R` reducing to them, whose image is identified with the point of `c` compatibly with the
legs. -/
structure MatrixModel where
  /-- The ranks. -/
  r : ℤ → ℕ
  /-- A lower bound of the ranks. -/
  lo : ℤ
  /-- An upper bound of the ranks. -/
  hi : ℤ
  r_lo (i : ℤ) : i < lo → r i = 0
  r_hi (i : ℤ) : hi < i → r i = 0
  /-- The level models. -/
  level (n : ℕ) : T.LevelModel r n
  isSucc (n : ℕ) : (level n).IsSucc (level (n + 1))
  /-- The matrix complex over `R`. -/
  L : MatrixComplex r R
  L_map (n : ℕ) (i : ℤ) : (L.d i).map (π n) = (level n).M.d i
  /-- The identification of the image of `L` with the point of the cone. -/
  iso : DerivedCategory.Q.obj L.complex ≅ c.pt
  iso_hom_π (n : ℕ) : iso.hom ≫ c.π.app (op n) =
    DerivedCategory.Q.map (L.reduction (π n) (level n).M (L_map n)) ≫
      (ModuleCat.restrictScalars.{u} (π n)).mapDerivedCategoryFactors.inv.app
        (level n).M.complex ≫ (derivedRestrictScalars (π n)).map (level n).iso.hom

variable {T} in
/-- The ranks of a matrix model vanish outside `[lo, hi]`. -/
lemma MatrixModel.r_eq_zero (m : T.MatrixModel c) {i : ℤ} (hi : i ∉ Finset.Icc m.lo m.hi) :
    m.r i = 0 := by
  rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hi
  rcases hi with hi | hi
  · exact m.r_lo i hi
  · exact m.r_hi i hi

include hπ hker hcomplete hsep hc in
/-- A normalized tower and a homotopy limit cone over it admit a matrix model. -/
theorem nonempty_matrixModel : Nonempty (T.MatrixModel c) := by
  obtain ⟨r, lo, hi, M₀, hlo, hhi, hM₀, ⟨e₀⟩⟩ :=
    MatrixComplex.exists_iso_Q_obj_of_isPerfect (T.isPerfect 0)
  let level := levelModelSeq hπ hker hhi ⟨M₀, hM₀, e₀⟩
  have hs (n : ℕ) : (level n).IsSucc (level (n + 1)) := LevelModel.isSucc_succ hπ hker hhi _
  let L := MatrixComplex.towerLim (fun n ↦ (level n).M) (fun n ↦ (hs n).1) hcomplete hsep
  have hL := MatrixComplex.map_towerLim_d (fun n ↦ (level n).M) (fun n ↦ (hs n).1) hcomplete hsep
  have hρs (n : ℕ) : Function.Surjective (ρ n) := Function.Surjective.of_comp (g := π (n + 1))
    (by
      rw [← RingHom.coe_comp, ← hρ n]
      exact hπ n)
  obtain ⟨f, hf⟩ := IsHomotopyLimit.exists_iso_of_iso (asIso (towerHom level hs))
    (MatrixComplex.isHomotopyLimit_towerCone hρ _ L hL hcomplete hsep hρs) hc
  exact ⟨⟨r, lo, hi, hlo, hhi, level, hs, L, hL, f, hf⟩⟩

variable {T} in
include hπ in
/-- The inductive step of the construction of lifts: a chain-level representative `E` at level
`n` of a compatible family extends to a representative at level `n + 1` whose reduction is
`E`, by correcting an arbitrary representative with a lifted homotopy. -/
lemma MatrixModel.exists_lift_succ (m : T.MatrixModel c) {f : ∀ n, T.obj n ⟶ T.obj n}
    (hf : T.IsCompatible f) (n : ℕ) (E : (m.level n).M.complex ⟶ (m.level n).M.complex)
    (hE : DerivedCategory.Q.map E = (m.level n).iso.hom ≫ f n ≫ (m.level n).iso.inv) :
    ∃ E' : (m.level (n + 1)).M.complex ⟶ (m.level (n + 1)).M.complex,
      DerivedCategory.Q.map E' = (m.level (n + 1)).iso.hom ≫ f (n + 1) ≫
        (m.level (n + 1)).iso.inv ∧
      E' ≫ (m.level (n + 1)).M.reduction (ρ n) (m.level n).M (m.isSucc n).1 =
        (m.level (n + 1)).M.reduction (ρ n) (m.level n).M (m.isSucc n).1 ≫
          ((ModuleCat.restrictScalars.{u} (ρ n)).mapHomologicalComplex _).map E := by
  have := (m.level (n + 1)).M.isStrictlyLE_complex m.hi m.r_hi
  obtain ⟨G, hG⟩ := DerivedCategory.Q_map_surjective_of_projective (m.level (n + 1)).M.complex
    (m.level (n + 1)).M.complex m.hi
    ((m.level (n + 1)).iso.hom ≫ f (n + 1) ≫ (m.level (n + 1)).iso.inv)
  have hρs : Function.Surjective (ρ n) := Function.Surjective.of_comp (g := π (n + 1)) (by
    rw [← RingHom.coe_comp, ← hρ n]
    exact hπ n)
  have h₁ := (m.isSucc n).2
  have key : DerivedCategory.Q.map (G ≫ (m.level (n + 1)).M.reduction (ρ n) (m.level n).M
      (m.isSucc n).1) = DerivedCategory.Q.map ((m.level (n + 1)).M.reduction (ρ n) (m.level n).M
        (m.isSucc n).1 ≫
          ((ModuleCat.restrictScalars.{u} (ρ n)).mapHomologicalComplex _).map E) := by
    rw [← cancel_mono ((ModuleCat.restrictScalars.{u} (ρ n)).mapDerivedCategoryFactors.inv.app
      (m.level n).M.complex ≫ (derivedRestrictScalars (ρ n)).map (m.level n).iso.hom)]
    simp only [Functor.map_comp, Category.assoc]
    rw [h₁, hG, Functor.mapDerivedCategoryFactors_inv_naturality_assoc, ← Functor.map_comp, hE]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Iso.inv_hom_id_assoc,
      Functor.map_comp]
    rw [reassoc_of% h₁, hf n]
  obtain ⟨H⟩ := (DerivedCategory.Q_map_eq_Q_map_iff_of_projective m.hi _ _).1 key
  obtain ⟨P, ⟨HP⟩, hP⟩ := (m.level (n + 1)).M.exists_comp_reduction_eq_sub (ρ n) hρs
    (N := (m.level (n + 1)).M) (m.isSucc n).1 H
  refine ⟨G - P, ?_, ?_⟩
  · rw [Functor.map_sub, hG, (DerivedCategory.Q_map_eq_Q_map_iff_of_projective m.hi P 0).2 ⟨HP⟩,
      Functor.map_zero, sub_zero]
  · rw [Preadditive.sub_comp, hP, sub_sub_cancel]

variable {T} in
/-- A sequence of chain-level representatives of a compatible family on the level models of a
matrix model, compatible with the reductions. -/
noncomputable def MatrixModel.liftSeq (m : T.MatrixModel c) {f : ∀ n, T.obj n ⟶ T.obj n}
    (hf : T.IsCompatible f) (E₀ : (m.level 0).M.complex ⟶ (m.level 0).M.complex)
    (hE₀ : DerivedCategory.Q.map E₀ = (m.level 0).iso.hom ≫ f 0 ≫ (m.level 0).iso.inv) :
    ∀ n, {E : (m.level n).M.complex ⟶ (m.level n).M.complex //
      DerivedCategory.Q.map E = (m.level n).iso.hom ≫ f n ≫ (m.level n).iso.inv}
  | 0 => ⟨E₀, hE₀⟩
  | n + 1 => ⟨(m.exists_lift_succ hπ hf n (m.liftSeq hf E₀ hE₀ n).1
      (m.liftSeq hf E₀ hE₀ n).2).choose, (m.exists_lift_succ hπ hf n (m.liftSeq hf E₀ hE₀ n).1
      (m.liftSeq hf E₀ hE₀ n).2).choose_spec.1⟩

variable {T} in
/-- The sequence `MatrixModel.liftSeq` is compatible with the reductions. -/
lemma MatrixModel.liftSeq_succ_comp (m : T.MatrixModel c) {f : ∀ n, T.obj n ⟶ T.obj n}
    (hf : T.IsCompatible f) (E₀ : (m.level 0).M.complex ⟶ (m.level 0).M.complex)
    (hE₀ : DerivedCategory.Q.map E₀ = (m.level 0).iso.hom ≫ f 0 ≫ (m.level 0).iso.inv)
    (n : ℕ) :
    (m.liftSeq hπ hf E₀ hE₀ (n + 1)).1 ≫
        (m.level (n + 1)).M.reduction (ρ n) (m.level n).M (m.isSucc n).1 =
      (m.level (n + 1)).M.reduction (ρ n) (m.level n).M (m.isSucc n).1 ≫
        ((ModuleCat.restrictScalars.{u} (ρ n)).mapHomologicalComplex _).map
          (m.liftSeq hπ hf E₀ hE₀ n).1 :=
  (m.exists_lift_succ hπ hf n (m.liftSeq hπ hf E₀ hE₀ n).1
    (m.liftSeq hπ hf E₀ hE₀ n).2).choose_spec.2

variable {T} in
include hπ hker in
/-- If `V` is a lift of a family `f` and `G` is a chain-level representative of `V` on the
matrix complex `L` of a matrix model, then the reduction of `G` at level `n` represents `f n`
on the level model. -/
lemma MatrixModel.Q_map_mapHom_comp (m : T.MatrixModel c) {f : ∀ n, T.obj n ⟶ T.obj n}
    {V : c.pt ⟶ c.pt} (hV : T.IsLift c f V) (G : m.L.complex ⟶ m.L.complex)
    (hG : DerivedCategory.Q.map G = m.iso.hom ≫ V ≫ m.iso.inv) (n : ℕ) :
    DerivedCategory.Q.map (MatrixComplex.mapHom (π n) (m.L_map n) (m.L_map n) G) ≫
      (m.level n).iso.hom = (m.level n).iso.hom ≫ f n := by
  refine (m.L.isDerivedBaseChange_reduction (π n) (hπ n) (hker n) m.lo m.hi m.r_lo m.r_hi
    (m.level n).M (m.L_map n) (T.obj n)).1 ?_
  have h := m.iso_hom_π n
  dsimp only
  simp only [Functor.map_comp, Category.assoc]
  rw [← Functor.mapDerivedCategoryFactors_inv_naturality_assoc, ← Functor.map_comp_assoc,
    ← MatrixComplex.comp_reduction_mapHom, Functor.map_comp_assoc, hG]
  simp only [Category.assoc]
  rw [← h, Iso.inv_hom_id_assoc, hV n, reassoc_of% h]


include hπ hker hcomplete hsep hc in
/-- Stacks Tag 09AW: the derived limit `P = R lim_n Res Q n` of a normalized tower of perfect
complexes is represented by a bounded complex of finite free `R`-modules. -/
theorem exists_iso_Q_obj_of_isHomotopyLimit :
    ∃ (M : CochainComplex (ModuleCat.{u} R) ℤ) (a b : ℤ), M.IsStrictlyGE a ∧ M.IsStrictlyLE b ∧
      (∀ i, Module.Free R (M.X i) ∧ Module.Finite R (M.X i)) ∧
      Nonempty (c.pt ≅ DerivedCategory.Q.obj M) := by
  obtain ⟨m⟩ := T.nonempty_matrixModel hπ hker hcomplete hsep hc
  exact ⟨m.L.complex, m.lo, m.hi, m.L.isStrictlyGE_complex m.lo m.r_lo,
    m.L.isStrictlyLE_complex m.hi m.r_hi, fun i ↦ ⟨inferInstance, inferInstance⟩, ⟨m.iso.symm⟩⟩

include hπ hker hcomplete hsep hc in
/-- The derived limit of a normalized tower of perfect complexes is perfect. -/
theorem isPerfect_pt : c.pt.IsPerfect := by
  obtain ⟨M, a, b, ha, hb, hM, ⟨e⟩⟩ := T.exists_iso_Q_obj_of_isHomotopyLimit hπ hker hcomplete
    hsep hc
  exact ⟨M, a, b, ha, hb, fun i ↦ ⟨haveI := (hM i).1; Module.Projective.of_free, (hM i).2⟩, ⟨e⟩⟩

include hπ hker hcomplete hsep hc in
/-- Every leg `pr_n : P ⟶ Res Q n` of the derived limit exhibits `Q n` as `P ⊗ᴸ_R A n`, i.e. the
adjoint map `π_n : P ⊗ᴸ_R A n ⟶ Q n` is an isomorphism. -/
theorem isDerivedBaseChange_π_app (n : ℕ) :
    IsDerivedBaseChange (f := π n) (c.π.app (op n)) := by
  obtain ⟨m⟩ := T.nonempty_matrixModel hπ hker hcomplete hsep hc
  have h := IsDerivedBaseChange.of_iso m.iso.symm
    ((m.L.isDerivedBaseChange_reduction (π n) (hπ n) (hker n) m.lo m.hi m.r_lo m.r_hi
      (m.level n).M (m.L_map n)).comp_map_iso (m.level n).iso)
  rw [← Iso.inv_hom_id_assoc m.iso (c.π.app (op n)), m.iso_hom_π n]
  simpa only [Iso.symm_hom, Category.assoc] using h

include hπ hker hcomplete hsep hc in
/-- Every compatible family of endomorphisms of the levels lifts to an endomorphism of the derived
limit. -/
theorem exists_isLift {f : ∀ n, T.obj n ⟶ T.obj n} (hf : T.IsCompatible f) :
    ∃ V : c.pt ⟶ c.pt, T.IsLift c f V := by
  obtain ⟨m⟩ := T.nonempty_matrixModel hπ hker hcomplete hsep hc
  have := (m.level 0).M.isStrictlyLE_complex m.hi m.r_hi
  obtain ⟨E₀, hE₀⟩ := DerivedCategory.Q_map_surjective_of_projective (m.level 0).M.complex
    (m.level 0).M.complex m.hi ((m.level 0).iso.hom ≫ f 0 ≫ (m.level 0).iso.inv)
  let E := m.liftSeq hπ hf E₀ hE₀
  have hE (n : ℕ) (i : ℤ) : (MatrixComplex.toMatrix (E (n + 1)).1 i).map (ρ n) =
      MatrixComplex.toMatrix (E n).1 i :=
    MatrixComplex.map_toMatrix_of_comp_reduction (ρ n) (m.isSucc n).1 (m.isSucc n).1 _ _
      (m.liftSeq_succ_comp hπ hf E₀ hE₀ n) i
  let E' := MatrixComplex.towerLimHom hcomplete hsep m.L m.L_map (fun n ↦ (E n).1) hE
  refine ⟨m.iso.inv ≫ DerivedCategory.Q.map E' ≫ m.iso.hom, fun n ↦ ?_⟩
  rw [← Iso.inv_hom_id_assoc m.iso (c.π.app (op n)), m.iso_hom_π n]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Functor.map_comp_assoc, MatrixComplex.reduction_naturality (π n) (m.L_map n) (m.L_map n)
    E' (E n).1 (MatrixComplex.map_toMatrix_towerLimHom hcomplete hsep m.L m.L_map _ hE n),
    Functor.map_comp_assoc, Functor.mapDerivedCategoryFactors_inv_naturality_assoc,
    ← Functor.map_comp, (E n).2, ← Functor.map_comp]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Functor.map_comp]

section Trace

/-! The braiding of the derived categories is the Koszul braiding
`DerivedCategory.braidedCategory'` of the derived tensor product. -/

attribute [local instance] DerivedCategory.braidedCategory'

variable [Abelian.HasFunctorialFlatResolution (ModuleCat.{u} R)]
  [∀ n, Abelian.HasFunctorialFlatResolution (ModuleCat.{u} (A n))]
  [HasRightDual c.pt] [∀ n, HasRightDual (T.obj n)]

omit [∀ n, Abelian.HasFunctorialFlatResolution (ModuleCat.{u} (A n))]
  [HasRightDual c.pt] [∀ n, HasRightDual (T.obj n)] in
include hπ hker hcomplete hsep hc in
/-- A right dual of the derived limit, chosen using its perfectness (`isPerfect_pt`). The trace
statements below hold for every right dual of `c.pt`, so in particular for this one. -/
@[instance_reducible]
noncomputable def hasRightDualPt : HasRightDual c.pt :=
  (T.isPerfect_pt hπ hker hcomplete hsep hc).isDualizable.some

omit [Abelian.HasFunctorialFlatResolution (ModuleCat.{u} R)]
  [HasRightDual c.pt] [∀ n, HasRightDual (T.obj n)] in
/-- A right dual of the level `n`, chosen using its perfectness. The trace statements below hold
for every right dual of `T.obj n`, so in particular for this one. -/
@[instance_reducible]
noncomputable def hasRightDualObj (n : ℕ) : HasRightDual (T.obj n) :=
  (T.isPerfect n).isDualizable.some

omit [∀ n, Abelian.HasFunctorialFlatResolution (ModuleCat.{u} (A n))]
  [∀ n, HasRightDual (T.obj n)] in
variable {T} in
/-- The trace of an endomorphism `V` of the point of the cone is the alternating sum of the
traces of a chain-level representative of `V` on the matrix complex `L` of a matrix model. -/
lemma MatrixModel.trace_eq (m : T.MatrixModel c) (V : c.pt ⟶ c.pt) (G : m.L.complex ⟶ m.L.complex)
    (hG : DerivedCategory.Q.map G = m.iso.hom ≫ V ≫ m.iso.inv) :
    MonoidalCategory.trace V = (algebraMap R (End (𝟙_ (DerivedCategory (ModuleCat.{u} R))))
      (∑ i ∈ Finset.Icc m.lo m.hi,
        (i.negOnePow : ℤ) • LinearMap.trace R (m.L.complex.X i) (G.f i).hom)).asHom :=
  DerivedCategory.trace_eq_algebraMap_sum_negOnePow_linearMapTrace m.L.complex G _
    (fun _ hi ↦ m.L.isZero_complex_X (m.r_eq_zero hi)) (fun _ ↦ inferInstance)
    (fun _ ↦ inferInstance) c.pt V m.iso.symm (by rw [Iso.symm_hom, hG, Iso.inv_hom_id_assoc])

omit [Abelian.HasFunctorialFlatResolution (ModuleCat.{u} R)]
  [HasRightDual c.pt] in
include hπ hker in
variable {T} in
/-- The trace of `f n`, for a family `f` lifted by `V`, is the reduction of the alternating sum of
the traces of a chain-level representative of `V` on the matrix complex `L`. -/
lemma MatrixModel.trace_f_eq (m : T.MatrixModel c) {f : ∀ n, T.obj n ⟶ T.obj n}
    {V : c.pt ⟶ c.pt} (hV : T.IsLift c f V) (G : m.L.complex ⟶ m.L.complex)
    (hG : DerivedCategory.Q.map G = m.iso.hom ≫ V ≫ m.iso.inv) (n : ℕ) :
    MonoidalCategory.trace (f n) =
      (algebraMap (A n) (End (𝟙_ (DerivedCategory (ModuleCat.{u} (A n)))))
        (π n (∑ i ∈ Finset.Icc m.lo m.hi,
          (i.negOnePow : ℤ) • LinearMap.trace R (m.L.complex.X i) (G.f i).hom))).asHom := by
  rw [MatrixComplex.map_sum_negOnePow_trace (π n) (m.L_map n) G]
  exact DerivedCategory.trace_eq_algebraMap_sum_negOnePow_linearMapTrace _ _ _
    (fun _ hi ↦ (m.level n).M.isZero_complex_X (m.r_eq_zero hi)) (fun _ ↦ inferInstance)
    (fun _ ↦ inferInstance) (T.obj n) (f n) (m.level n).iso.symm (by
      rw [Iso.symm_hom, Iso.comp_inv_eq, Category.assoc, m.Q_map_mapHom_comp hπ hker hV G hG n,
        Iso.inv_hom_id_assoc])

-- The compatibility `hf` of the blueprint statement is not needed.
set_option linter.unusedVariables false in
include hπ hker hcomplete hsep hc in
/-- The categorical trace of a lift `V` of a compatible family `f` reduces to the traces of the
`f n`: there is `r : R` with `tr_R(V ∣ P) = r` and `tr_{A n}(f n ∣ Q n) = r mod ϖⁿ⁺¹` for all `n`.
-/
theorem exists_trace_eq_of_isLift {f : ∀ n, T.obj n ⟶ T.obj n} (hf : T.IsCompatible f)
    {V : c.pt ⟶ c.pt} (hV : T.IsLift c f V) :
    ∃ r : R,
      MonoidalCategory.trace V = (algebraMap R (End (𝟙_ (DerivedCategory (ModuleCat.{u} R))))
        r).asHom ∧
      ∀ n, MonoidalCategory.trace (f n) =
        (algebraMap (A n) (End (𝟙_ (DerivedCategory (ModuleCat.{u} (A n))))) (π n r)).asHom := by
  obtain ⟨m⟩ := T.nonempty_matrixModel hπ hker hcomplete hsep hc
  have := m.L.isStrictlyLE_complex m.hi m.r_hi
  obtain ⟨G, hG⟩ := DerivedCategory.Q_map_surjective_of_projective m.L.complex m.L.complex m.hi
    (m.iso.hom ≫ V ≫ m.iso.inv)
  exact ⟨_, m.trace_eq V G hG, m.trace_f_eq hπ hker hV G hG⟩

-- The compatibility `hf` of the blueprint statement is not needed.
set_option linter.unusedVariables false in
set_option linter.unusedSectionVars false in
include hπ hker hcomplete hsep hc in
/-- The categorical trace of a lift of a compatible family does not depend on the lift. -/
theorem trace_eq_of_isLift {f : ∀ n, T.obj n ⟶ T.obj n} (hf : T.IsCompatible f)
    {V V' : c.pt ⟶ c.pt} (hV : T.IsLift c f V) (hV' : T.IsLift c f V') :
    MonoidalCategory.trace V = MonoidalCategory.trace V' := by
  obtain ⟨m⟩ := T.nonempty_matrixModel hπ hker hcomplete hsep hc
  have := m.L.isStrictlyLE_complex m.hi m.r_hi
  obtain ⟨G, hG⟩ := DerivedCategory.Q_map_surjective_of_projective m.L.complex m.L.complex m.hi
    (m.iso.hom ≫ V ≫ m.iso.inv)
  obtain ⟨G', hG'⟩ := DerivedCategory.Q_map_surjective_of_projective m.L.complex m.L.complex
    m.hi (m.iso.hom ≫ V' ≫ m.iso.inv)
  rw [m.trace_eq V G hG, m.trace_eq V' G' hG']
  congr 2
  refine MatrixComplex.eq_of_forall_π hsep fun n ↦ ?_
  rw [MatrixComplex.map_sum_negOnePow_trace (π n) (m.L_map n) G,
    MatrixComplex.map_sum_negOnePow_trace (π n) (m.L_map n) G']
  have hQ : DerivedCategory.Q.map (MatrixComplex.mapHom (π n) (m.L_map n) (m.L_map n) G) =
      DerivedCategory.Q.map (MatrixComplex.mapHom (π n) (m.L_map n) (m.L_map n) G') := by
    rw [← cancel_mono (m.level n).iso.hom, m.Q_map_mapHom_comp hπ hker hV G hG n,
      m.Q_map_mapHom_comp hπ hker hV' G' hG' n]
  have := (m.level n).M.isStrictlyLE_complex m.hi m.r_hi
  obtain ⟨H⟩ := (DerivedCategory.Q_map_eq_Q_map_iff_of_projective m.hi _ _).1 hQ
  rcases le_or_gt (m.lo - 1) m.hi with hab | hab
  · exact CochainComplex.sum_negOnePow_trace_eq_of_homotopy H m.lo m.hi hab
      ((m.level n).M.isZero_complex_X (m.r_lo _ (by omega)))
      ((m.level n).M.isZero_complex_X (m.r_hi _ (by omega)))
  · rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty, Finset.sum_empty]

end Trace

end NormalizedPerfectTower

end ModuleCat
