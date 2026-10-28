import Langlands.Cohomology.DivisibleSystem.CompatibleHomComplex

/-!
# Degree zero cocycles of the complex of compatible families

Harris, *Galois properties of cohomological automorphic forms on GL(n)*, proof of
Proposition 4.10, pp.311-312, passes from the complexes (4.10.2) at the finite levels `m`
to their inverse limit along the maps (4.10.3). `DivisibleSystem.HomSystem` gives the
corresponding inverse system `homComplexSystem R T W`, `m ↦ Hom^•(T m, W m)`, for
`ℓ`-divisible systems `T` and `W` of cochain complexes, and
`DivisibleSystem.CompatibleHomComplex` describes its limit as the complex
`compatibleHomComplex R T W` of compatible families of graded morphisms.

This module identifies the degree `0` cocycles of these complexes. A `0`-cochain
`T m ⟶ W m` is a cocycle exactly when it is a chain map (Mathlib's `Cocycle.homOf` and
`Cocycle.ofHom`), and on chain maps the transition `cochainTransition` of graded morphisms
is the transition `homTransition` of the `ℓ`-divisible systems `T` and `W` in the abelian
category of cochain complexes. Hence a compatible family of degree `0` cocycles is a
family of chain maps `T m ⟶ W m` commuting with the projections, i.e. a morphism of the
inverse systems `T.tower ⟶ W.tower`. This gives an `R`-linear equivalence between
`T.tower ⟶ W.tower` and the kernel of the differential of `compatibleHomComplex R T W`
in degree `0`, and through `compatibleHomComplexIsoLimit` with the kernel of the
differential of `homComplexLimit R T W` in degree `0`.

Homotopies, the cohomology of these complexes, Ext groups and the identification of
Harris's complexes (4.10.2) with Hom complexes are not part of this module.
-/

noncomputable section

namespace Langlands.Cohomology

open CategoryTheory CategoryTheory.Limits Opposite
open CochainComplex.HomComplex

universe w v u

/-- The `0`-cochain of a scalar multiple of a chain map. -/
lemma cochain_ofHom_smul {R : Type w} [Ring R] {C : Type u} [Category.{v} C] [Preadditive C]
    [Linear R C] {F G : CochainComplex C ℤ} (r : R) (f : F ⟶ G) :
    Cochain.ofHom (r • f) = r • Cochain.ofHom f :=
  Cochain.ext₀ _ _ fun p => by
    rw [Cochain.smul_v, Cochain.ofHom_v, Cochain.ofHom_v, HomologicalComplex.smul_f_apply]

/-- An isomorphism of complexes of modules restricts to an isomorphism between the
kernels of the differentials `K.d i j` and `L.d i j`. -/
def kerDLinearEquivOfIso {R : Type w} [Ring R] {K L : CochainComplex (ModuleCat.{v} R) ℤ}
    (e : K ≅ L) (i j : ℤ) :
    LinearMap.ker (K.d i j).hom ≃ₗ[R] LinearMap.ker (L.d i j).hom where
  toFun x := ⟨(e.hom.f i).hom x.1, by
    rw [LinearMap.mem_ker]
    have h := congrArg (fun g => g.hom x.1) (e.hom.comm i j)
    refine h.trans ?_
    change (e.hom.f j).hom ((K.d i j).hom x.1) = 0
    rw [LinearMap.mem_ker.1 x.2, map_zero]⟩
  map_add' x y := Subtype.ext ((e.hom.f i).hom.map_add x.1 y.1)
  map_smul' r x := Subtype.ext ((e.hom.f i).hom.map_smul r x.1)
  invFun y := ⟨(e.inv.f i).hom y.1, by
    rw [LinearMap.mem_ker]
    have h := congrArg (fun g => g.hom y.1) (e.inv.comm i j)
    refine h.trans ?_
    change (e.inv.f j).hom ((L.d i j).hom y.1) = 0
    rw [LinearMap.mem_ker.1 y.2, map_zero]⟩
  left_inv x := Subtype.ext (congrArg (fun g => g.hom x.1)
    (HomologicalComplex.congr_hom e.hom_inv_id i))
  right_inv y := Subtype.ext (congrArg (fun g => g.hom y.1)
    (HomologicalComplex.congr_hom e.inv_hom_id i))

lemma kerDLinearEquivOfIso_apply_coe {R : Type w} [Ring R]
    {K L : CochainComplex (ModuleCat.{v} R) ℤ} (e : K ≅ L) (i j : ℤ)
    (x : LinearMap.ker (K.d i j).hom) :
    (kerDLinearEquivOfIso e i j x).1 = (e.hom.f i).hom x.1 :=
  rfl

namespace DivisibleSystem

section ChainMaps

variable {C : Type u} [Category.{v} C] [Abelian C] {ℓ : ℕ}
  (T W : DivisibleSystem (CochainComplex C ℤ) ℓ)

/-- The transition `homTransition` of chain maps between `ℓ`-divisible systems of cochain
complexes is computed degreewise. -/
lemma homTransition_f {m' m : ℕ} (h : m' ≤ m) (f : T.obj m ⟶ W.obj m) (p : ℤ) :
    (homTransition T W h f).f p = homTransition (T.degree p) (W.degree p) h (f.f p) := by
  symm
  refine (homTransition_eq_iff (T.degree p) (W.degree p) h (f.f p) _).2 ?_
  exact HomologicalComplex.congr_hom (projection_comp_homTransition T W h f) p

/-- On chain maps, the transition of graded morphisms is the transition `homTransition`
of chain maps. -/
lemma cochainTransition_ofHom {m' m : ℕ} (h : m' ≤ m) (f : T.obj m ⟶ W.obj m) :
    cochainTransition T W h (Cochain.ofHom f) = Cochain.ofHom (homTransition T W h f) := by
  rw [cochainTransition_eq_iff, ← Cochain.ofHom_comp, ← Cochain.ofHom_comp,
    projection_comp_homTransition]

end ChainMaps

section CompatibleCocycles

variable (R : Type w) [Ring R] {C : Type u} [Category.{v} C] [Abelian C] [Linear R C]
  {ℓ : ℕ} (T W : DivisibleSystem (CochainComplex C ℤ) ℓ)

/-- The degree `0` cocycles of `compatibleHomComplex R T W`: the kernel of its
differential from degree `0` to degree `1`. -/
def compatibleCocycles : Submodule R (compatibleCochains R T W 0) :=
  LinearMap.ker (compatibleδ R T W 0 1)

lemma compatibleCocycles_eq_ker_d :
    compatibleCocycles R T W = LinearMap.ker ((compatibleHomComplex R T W).d 0 1).hom :=
  rfl

/-- A compatible family of `0`-cochains is a cocycle exactly when every member is a
cocycle. -/
lemma mem_compatibleCocycles_iff (z : compatibleCochains R T W 0) :
    z ∈ compatibleCocycles R T W ↔ ∀ m : ℕ, δ 0 1 (z.1 m) = 0 := by
  rw [compatibleCocycles, LinearMap.mem_ker]
  constructor
  · intro hz m
    exact congrArg (fun y => y.1 m) hz
  · intro hz
    exact Subtype.ext (funext hz)

/-- The member at level `m` of a compatible family of degree `0` cocycles, as a
`0`-cocycle of the Hom complex of level `m`. -/
def compatibleCocycleAt (z : compatibleCocycles R T W) (m : ℕ) :
    Cocycle (T.obj m) (W.obj m) 0 :=
  Cocycle.mk (z.1.1 m) 1 (zero_add 1) ((mem_compatibleCocycles_iff R T W z.1).1 z.2 m)

/-- The chain map `T m ⟶ W m` given by the member at level `m` of a compatible family of
degree `0` cocycles. -/
def compatibleCocycleHom (z : compatibleCocycles R T W) (m : ℕ) : T.obj m ⟶ W.obj m :=
  Cocycle.homOf (compatibleCocycleAt R T W z m)

lemma compatibleCocycleHom_f (z : compatibleCocycles R T W) (m : ℕ) (p : ℤ) :
    (compatibleCocycleHom R T W z m).f p = (z.1.1 m).v p p (add_zero p) :=
  rfl

lemma ofHom_compatibleCocycleHom (z : compatibleCocycles R T W) (m : ℕ) :
    Cochain.ofHom (compatibleCocycleHom R T W z m) = z.1.1 m :=
  Cocycle.cochain_ofHom_homOf_eq_coe _

/-- The chain maps given by a compatible family of degree `0` cocycles are fixed by the
transitions `homTransition`. -/
lemma homTransition_compatibleCocycleHom (z : compatibleCocycles R T W) {m' m : ℕ}
    (h : m' ≤ m) :
    homTransition T W h (compatibleCocycleHom R T W z m) = compatibleCocycleHom R T W z m' := by
  apply Cochain.ofHom_injective
  rw [← cochainTransition_ofHom, ofHom_compatibleCocycleHom, ofHom_compatibleCocycleHom]
  exact z.1.2 h

/-- The morphism of inverse systems `T.tower ⟶ W.tower` given by a compatible family of
degree `0` cocycles. -/
@[simps]
def towerHomOfCompatibleCocycle (z : compatibleCocycles R T W) : T.tower ⟶ W.tower where
  app m := compatibleCocycleHom R T W z m.unop
  naturality _ _ φ := (homTransition_eq_iff T W (leOfHom φ.unop) _ _).1
    (homTransition_compatibleCocycleHom R T W z (leOfHom φ.unop))

/-- The compatible family of degree `0` cocycles given by a morphism of inverse systems
`T.tower ⟶ W.tower`: its member at level `m` is the `0`-cochain of the component at
`m`. -/
def compatibleCocycleOfTowerHom (α : T.tower ⟶ W.tower) : compatibleCocycles R T W :=
  ⟨⟨fun m => Cochain.ofHom (α.app (op m)), fun m' m h => by
      rw [cochainTransition_ofHom, homTransition_app]⟩,
    (mem_compatibleCocycles_iff R T W _).2 fun m => δ_ofHom (α.app (op m))⟩

lemma compatibleCocycleOfTowerHom_coe (α : T.tower ⟶ W.tower) (m : ℕ) :
    (compatibleCocycleOfTowerHom R T W α).1.1 m = Cochain.ofHom (α.app (op m)) :=
  rfl

/-- The morphisms of the inverse systems `T.tower ⟶ W.tower` are the compatible families
of degree `0` cocycles of the Hom complexes, i.e. the degree `0` cocycles of
`compatibleHomComplex R T W`. -/
def towerHomEquivCompatibleCocycles : (T.tower ⟶ W.tower) ≃ₗ[R] compatibleCocycles R T W where
  toFun := compatibleCocycleOfTowerHom R T W
  map_add' α β := Subtype.ext (Subtype.ext (funext fun m =>
    (congrArg Cochain.ofHom (NatTrans.app_add (op m) α β)).trans (Cochain.ofHom_add _ _)))
  map_smul' r α := Subtype.ext (Subtype.ext (funext fun m =>
    (congrArg Cochain.ofHom (NatTrans.app_smul (op m) r α)).trans
      (cochain_ofHom_smul r (α.app (op m)))))
  invFun := towerHomOfCompatibleCocycle R T W
  left_inv α := by
    refine NatTrans.ext (funext fun m => ?_)
    apply Cochain.ofHom_injective
    exact ofHom_compatibleCocycleHom R T W (compatibleCocycleOfTowerHom R T W α) m.unop
  right_inv z := Subtype.ext (Subtype.ext (funext fun m =>
    ofHom_compatibleCocycleHom R T W z m))

@[simp]
lemma towerHomEquivCompatibleCocycles_apply_coe (α : T.tower ⟶ W.tower) (m : ℕ) :
    (towerHomEquivCompatibleCocycles R T W α).1.1 m = Cochain.ofHom (α.app (op m)) :=
  rfl

@[simp]
lemma towerHomEquivCompatibleCocycles_symm_apply_app (z : compatibleCocycles R T W)
    (m : ℕ) :
    ((towerHomEquivCompatibleCocycles R T W).symm z).app (op m) =
      compatibleCocycleHom R T W z m :=
  rfl

/-- The morphisms of the inverse systems `T.tower ⟶ W.tower` are the degree `0` cocycles
of the inverse limit `homComplexLimit R T W` of the Hom complexes. -/
def towerHomEquivLimitCocycles :
    (T.tower ⟶ W.tower) ≃ₗ[R] LinearMap.ker ((homComplexLimit R T W).d 0 1).hom :=
  (towerHomEquivCompatibleCocycles R T W).trans
    (kerDLinearEquivOfIso (compatibleHomComplexIsoLimit R T W) 0 1)

/-- The projection to level `m` of the degree `0` cocycle of `homComplexLimit R T W`
given by a morphism of inverse systems is the `0`-cochain of its component at `m`. -/
lemma limit_π_f_towerHomEquivLimitCocycles (α : T.tower ⟶ W.tower) (m : ℕ) :
    ((limit.π (homComplexSystem R T W) (op m)).f 0).hom
        (towerHomEquivLimitCocycles R T W α).1 =
      Cochain.ofHom (α.app (op m)) :=
  congrArg (fun g => (g.f 0).hom (towerHomEquivCompatibleCocycles R T W α).1)
    (compatibleHomComplexIsoLimit_hom_π R T W m)

/-- The projection to level `m` of a degree `0` cocycle of `homComplexLimit R T W` is the
`0`-cochain of the component at `m` of the corresponding morphism of inverse systems. -/
lemma limit_π_f_eq_ofHom_towerHomEquivLimitCocycles_symm_app
    (x : LinearMap.ker ((homComplexLimit R T W).d 0 1).hom) (m : ℕ) :
    ((limit.π (homComplexSystem R T W) (op m)).f 0).hom x.1 =
      Cochain.ofHom (((towerHomEquivLimitCocycles R T W).symm x).app (op m)) := by
  conv_lhs => rw [← LinearEquiv.apply_symm_apply (towerHomEquivLimitCocycles R T W) x]
  exact limit_π_f_towerHomEquivLimitCocycles R T W _ m

end CompatibleCocycles

end DivisibleSystem

section Smooth

variable (R : Type u) [CommRing R] (G : Type v) [Group G] [TopologicalSpace G] {ℓ : ℕ}

/-- For `ℓ`-divisible systems of cochain complexes of smooth representations, the
morphisms of the inverse systems, i.e. the compatible families of equivariant chain maps
`T m ⟶ W m`, are the degree `0` cocycles of the inverse limit of the Hom complexes of
equivariant maps. -/
abbrev smoothTowerHomEquivLimitCocycles
    (T W : SmoothRepComplexDivisibleSystem.{v, u, w} R G ℓ) :
    (T.tower ⟶ W.tower) ≃ₗ[R]
      LinearMap.ker ((DivisibleSystem.homComplexLimit R T W).d 0 1).hom :=
  DivisibleSystem.towerHomEquivLimitCocycles R T W

end Smooth

end Langlands.Cohomology
