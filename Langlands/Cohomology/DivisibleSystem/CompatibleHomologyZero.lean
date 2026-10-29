import Langlands.Cohomology.DivisibleSystem.CompatibleCocycle
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Degree zero cohomology of the complex of compatible families

Harris, *Galois properties of cohomological automorphic forms on GL(n)*, proof of
Proposition 4.10, pp.311-312, passes from the complexes (4.10.2) at the finite levels `m`
to their inverse limit along the maps (4.10.3). `DivisibleSystem.HomSystem` gives the
corresponding inverse system `homComplexSystem R T W` of Hom complexes for `ℓ`-divisible
systems `T` and `W` of cochain complexes, `DivisibleSystem.CompatibleHomComplex` describes
its limit as the complex `compatibleHomComplex R T W` of compatible families, and
`DivisibleSystem.CompatibleCocycle` identifies the degree `0` cocycles with the morphisms
of inverse systems `T.tower ⟶ W.tower`.

This module identifies the degree `0` coboundaries and cohomology. A morphism of inverse
systems `α` has a coboundary as cocycle exactly when it admits a compatible
null-homotopy: null-homotopies of the chain maps `α m` at all levels whose components
commute with the projections of `T` and `W`. The degree `0` cohomology of
`compatibleHomComplex R T W` is the quotient of the cocycles by the coboundaries (Mathlib's
`ShortComplex.moduleCatHomologyIso`), hence the quotient of `T.tower ⟶ W.tower` by the
morphisms admitting a compatible null-homotopy, i.e. the compatible homotopy classes of
morphisms of inverse systems; through `compatibleHomComplexIsoLimit` the same holds for
the degree `0` cohomology of `homComplexLimit R T W`.

Cohomology in nonzero degrees, Ext groups, morphisms in derived categories and the
identification of Harris's complexes (4.10.2) with Hom complexes are not part of this
module.
-/

noncomputable section

namespace Langlands.Cohomology

open CategoryTheory CategoryTheory.Limits Opposite
open CochainComplex.HomComplex

universe w v u

namespace DivisibleSystem

section CompatibleNullHomotopy

variable {C : Type u} [Category.{v} C] [Abelian C] {ℓ : ℕ}
  (T W : DivisibleSystem (CochainComplex C ℤ) ℓ)

/-- Homotopies at levels `m' ≤ m` commute with the projections exactly when the
transition sends the `(-1)`-cochain of the homotopy at level `m` to the one at level
`m'`. -/
lemma projection_comp_homotopy_hom_iff {m' m : ℕ} (h : m' ≤ m)
    {φ₁ φ₂ : T.obj m ⟶ W.obj m} {φ₁' φ₂' : T.obj m' ⟶ W.obj m'}
    (H : Homotopy φ₁ φ₂) (H' : Homotopy φ₁' φ₂') :
    (∀ p q : ℤ, (T.projection h).f p ≫ H'.hom p q = H.hom p q ≫ (W.projection h).f q) ↔
      cochainTransition T W h (Cochain.ofHomotopy H) = Cochain.ofHomotopy H' := by
  rw [cochainTransition_eq_iff]
  constructor
  · intro hc
    ext p q hpq
    rw [Cochain.zero_cochain_comp_v, Cochain.comp_zero_cochain_v, Cochain.ofHom_v,
      Cochain.ofHom_v]
    simp only [Cochain.ofHomotopy, Cochain.mk_v]
    exact hc p q
  · intro he p q
    by_cases hpq : p + (-1) = q
    · have := Cochain.congr_v he p q hpq
      rw [Cochain.zero_cochain_comp_v, Cochain.comp_zero_cochain_v, Cochain.ofHom_v,
        Cochain.ofHom_v] at this
      simpa only [Cochain.ofHomotopy, Cochain.mk_v] using this
    · have hr : ¬ (ComplexShape.up ℤ).Rel q p := fun hr => hpq (by
        rw [ComplexShape.up_Rel] at hr
        omega)
      rw [H'.zero p q hr, H.zero p q hr, Limits.comp_zero, Limits.zero_comp]

/-- A compatible null-homotopy of a morphism of inverse systems `α : T.tower ⟶ W.tower`:
a null-homotopy of the chain map `α m : T m ⟶ W m` at every level `m`, such that the
components of the homotopies commute with the projections of `T` and `W`. -/
structure CompatibleNullHomotopy (α : T.tower ⟶ W.tower) where
  /-- The null-homotopy at level `m`. -/
  homotopy (m : ℕ) : Homotopy (α.app (op m)) 0
  /-- The components of the homotopies commute with the projections. -/
  comm ⦃m' m : ℕ⦄ (h : m' ≤ m) (p q : ℤ) :
    (T.projection h).f p ≫ (homotopy m').hom p q = (homotopy m).hom p q ≫ (W.projection h).f q

variable {T W}

/-- The `(-1)`-cochains of a compatible null-homotopy are compatible with the
transitions. -/
lemma CompatibleNullHomotopy.cochainTransition_ofHomotopy {α : T.tower ⟶ W.tower}
    (H : CompatibleNullHomotopy T W α) {m' m : ℕ} (h : m' ≤ m) :
    cochainTransition T W h (Cochain.ofHomotopy (H.homotopy m)) =
      Cochain.ofHomotopy (H.homotopy m') :=
  (projection_comp_homotopy_hom_iff T W h _ _).1 (H.comm h)

/-- The differential of the `(-1)`-cochain of the null-homotopy at level `m` is the
`0`-cochain of `α m`. -/
lemma CompatibleNullHomotopy.δ_ofHomotopy {α : T.tower ⟶ W.tower}
    (H : CompatibleNullHomotopy T W α) (m : ℕ) :
    δ (-1) 0 (Cochain.ofHomotopy (H.homotopy m)) = Cochain.ofHom (α.app (op m)) := by
  rw [CochainComplex.HomComplex.δ_ofHomotopy, Cochain.ofHom_zero, sub_zero]

/-- The compatible null-homotopy given by a family of `(-1)`-cochains that is compatible
with the transitions and whose differentials are the `0`-cochains of the components of
`α`. -/
def CompatibleNullHomotopy.ofCochains {α : T.tower ⟶ W.tower}
    (z : ∀ m : ℕ, Cochain (T.obj m) (W.obj m) (-1))
    (hz : ∀ ⦃m' m : ℕ⦄ (h : m' ≤ m), cochainTransition T W h (z m) = z m')
    (hδ : ∀ m : ℕ, δ (-1) 0 (z m) = Cochain.ofHom (α.app (op m))) :
    CompatibleNullHomotopy T W α where
  homotopy m := (Cochain.equivHomotopy _ _).symm
    ⟨z m, by rw [Cochain.ofHom_zero, add_zero, hδ]⟩
  comm m' m h := by
    refine (projection_comp_homotopy_hom_iff T W h _ _).2 ?_
    have e : ∀ k : ℕ, Cochain.ofHomotopy ((Cochain.equivHomotopy (α.app (op k)) 0).symm
        ⟨z k, by rw [Cochain.ofHom_zero, add_zero, hδ]⟩) = z k := fun k =>
      congrArg Subtype.val ((Cochain.equivHomotopy (α.app (op k)) 0).apply_symm_apply
        ⟨z k, by rw [Cochain.ofHom_zero, add_zero, hδ]⟩)
    rw [e m, e m']
    exact hz h

/-- The `(-1)`-cochains of `CompatibleNullHomotopy.ofCochains z hz hδ` are the members
of `z`. -/
lemma CompatibleNullHomotopy.ofHomotopy_ofCochains {α : T.tower ⟶ W.tower}
    (z : ∀ m : ℕ, Cochain (T.obj m) (W.obj m) (-1))
    (hz : ∀ ⦃m' m : ℕ⦄ (h : m' ≤ m), cochainTransition T W h (z m) = z m')
    (hδ : ∀ m : ℕ, δ (-1) 0 (z m) = Cochain.ofHom (α.app (op m))) (m : ℕ) :
    Cochain.ofHomotopy ((CompatibleNullHomotopy.ofCochains z hz hδ).homotopy m) = z m :=
  congrArg Subtype.val ((Cochain.equivHomotopy (α.app (op m)) 0).apply_symm_apply
    ⟨z m, by rw [Cochain.ofHom_zero, add_zero, hδ]⟩)

end CompatibleNullHomotopy

section CompatibleCoboundaries

variable (R : Type w) [Ring R] {C : Type u} [Category.{v} C] [Abelian C] [Linear R C]
  {ℓ : ℕ} (T W : DivisibleSystem (CochainComplex C ℤ) ℓ)

/-- The additive group structure of the degree `0` cocycles of
`compatibleHomComplex R T W`, which is `Submodule.addCommGroup`. It is declared directly
because instance search does not find it through the two nested submodules when forming
quotients. -/
instance addCommGroupCompatibleCocycles : AddCommGroup (compatibleCocycles R T W) :=
  Submodule.addCommGroup _

/-- The differential of a compatible family of `(-1)`-cochains is a degree `0` cocycle. -/
lemma compatibleδ_mem_compatibleCocycles (y : compatibleCochains R T W (-1)) :
    compatibleδ R T W (-1) 0 y ∈ compatibleCocycles R T W :=
  (mem_compatibleCocycles_iff R T W _).2 fun m => δ_δ (-1) 0 1 (y.1 m)

/-- The degree `0` coboundaries of `compatibleHomComplex R T W`: the image of its
differential from degree `-1`, as a submodule of the degree `0` cocycles. -/
def compatibleCoboundaries : Submodule R (compatibleCocycles R T W) :=
  LinearMap.range ((compatibleδ R T W (-1) 0).codRestrict (compatibleCocycles R T W)
    (compatibleδ_mem_compatibleCocycles R T W))

/-- A degree `0` cocycle is a coboundary exactly when it is the levelwise differential of
a compatible family of `(-1)`-cochains. -/
lemma mem_compatibleCoboundaries_iff (z : compatibleCocycles R T W) :
    z ∈ compatibleCoboundaries R T W ↔
      ∃ y : compatibleCochains R T W (-1), ∀ m : ℕ, δ (-1) 0 (y.1 m) = z.1.1 m := by
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y, fun m => congrArg (fun x : compatibleCocycles R T W => x.1.1 m) hy⟩
  · rintro ⟨y, hy⟩
    exact ⟨y, Subtype.ext (Subtype.ext (funext hy))⟩

/-- The morphisms of inverse systems `T.tower ⟶ W.tower` whose degree `0` cocycle of
`compatibleHomComplex R T W` is a coboundary. -/
def nullHomotopicTowerHoms : Submodule R (T.tower ⟶ W.tower) :=
  (compatibleCoboundaries R T W).comap (towerHomEquivCompatibleCocycles R T W).toLinearMap

/-- A morphism of inverse systems lies in `nullHomotopicTowerHoms` exactly when its
`0`-cochains are the levelwise differentials of a compatible family of `(-1)`-cochains. -/
lemma mem_nullHomotopicTowerHoms_iff_exists_cochains (α : T.tower ⟶ W.tower) :
    α ∈ nullHomotopicTowerHoms R T W ↔
      ∃ y : compatibleCochains R T W (-1),
        ∀ m : ℕ, δ (-1) 0 (y.1 m) = Cochain.ofHom (α.app (op m)) :=
  mem_compatibleCoboundaries_iff R T W _

/-- A morphism of inverse systems `T.tower ⟶ W.tower` has a coboundary as degree `0`
cocycle exactly when it admits a compatible null-homotopy. -/
theorem mem_nullHomotopicTowerHoms_iff (α : T.tower ⟶ W.tower) :
    α ∈ nullHomotopicTowerHoms R T W ↔ Nonempty (CompatibleNullHomotopy T W α) := by
  rw [mem_nullHomotopicTowerHoms_iff_exists_cochains]
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨CompatibleNullHomotopy.ofCochains y.1 y.2 hy⟩
  · rintro ⟨H⟩
    exact ⟨⟨fun m => Cochain.ofHomotopy (H.homotopy m),
      fun _ _ h => H.cochainTransition_ofHomotopy h⟩, H.δ_ofHomotopy⟩

end CompatibleCoboundaries

section HomologyZero

variable (R : Type w) [Ring R] {C : Type u} [Category.{v} C] [Abelian C] [Linear R C]
  {ℓ : ℕ} (T W : DivisibleSystem (CochainComplex C ℤ) ℓ)

private lemma up_prev_zero : (ComplexShape.up ℤ).prev 0 = -1 :=
  (ComplexShape.up ℤ).prev_eq' (by simp)

private lemma up_next_zero : (ComplexShape.up ℤ).next 0 = 1 :=
  (ComplexShape.up ℤ).next_eq' (by simp)

/-- The degree `0` cohomology of `compatibleHomComplex R T W` is the quotient of the
degree `0` cocycles by the coboundaries: Mathlib's identification of the homology of a
short complex of modules with the kernel modulo the image, for the short complex in
degrees `-1, 0, 1`. -/
def compatibleHomologyZeroEquiv :
    (compatibleHomComplex R T W).homology 0 ≃ₗ[R]
      compatibleCocycles R T W ⧸ compatibleCoboundaries R T W :=
  ((compatibleHomComplex R T W).homologyIsoSc' (-1) 0 1 up_prev_zero up_next_zero ≪≫
    ((compatibleHomComplex R T W).sc' (-1) 0 1).moduleCatHomologyIso).toLinearEquiv

/-- The image of a degree `0` cycle of `compatibleHomComplex R T W` in the degree `0`
cochains is a cocycle. -/
lemma iCycles_mem_compatibleCocycles (x : (compatibleHomComplex R T W).cycles 0) :
    ((compatibleHomComplex R T W).iCycles 0).hom x ∈ compatibleCocycles R T W := by
  have h : compatibleδ R T W 0 1 (((compatibleHomComplex R T W).iCycles 0).hom x) = 0 :=
    congrArg (fun f => f.hom x) ((compatibleHomComplex R T W).iCycles_d 0 1)
  exact (LinearMap.mem_ker (f := compatibleδ R T W 0 1)).2 h

/-- Under `compatibleHomologyZeroEquiv`, the cohomology class of a degree `0` cycle is the
class of its image in the degree `0` cochains. -/
lemma compatibleHomologyZeroEquiv_homologyπ (x : (compatibleHomComplex R T W).cycles 0) :
    compatibleHomologyZeroEquiv R T W (((compatibleHomComplex R T W).homologyπ 0).hom x) =
      Submodule.Quotient.mk ⟨((compatibleHomComplex R T W).iCycles 0).hom x,
        iCycles_mem_compatibleCocycles R T W x⟩ := by
  let K := compatibleHomComplex R T W
  let S := K.sc' (-1) 0 1
  let c := (K.cyclesIsoSc' (-1) 0 1 up_prev_zero up_next_zero).hom.hom x
  have h₁ := congrArg (fun f => f.hom x)
    (K.π_homologyIsoSc'_hom (-1) 0 1 up_prev_zero up_next_zero)
  have h₂ := congrArg (fun f => f.hom c) S.π_moduleCatCyclesIso_hom
  have h₃ := congrArg (fun f => f.hom c) S.moduleCatCyclesIso_hom_i
  have h₄ := congrArg (fun f => f.hom x)
    (K.cyclesIsoSc'_hom_iCycles (-1) 0 1 up_prev_zero up_next_zero)
  exact ((congrArg S.moduleCatHomologyIso.hom.hom h₁).trans h₂).trans
    (congrArg (fun y : compatibleCocycles R T W =>
        (Submodule.Quotient.mk y : compatibleCocycles R T W ⧸ compatibleCoboundaries R T W))
      (Subtype.ext (h₃.trans h₄) : (S.moduleCatCyclesIso.hom.hom c : compatibleCocycles R T W) =
        ⟨((compatibleHomComplex R T W).iCycles 0).hom x, iCycles_mem_compatibleCocycles R T W x⟩))

/-- The cohomology class in degree `0` of `compatibleHomComplex R T W` of the degree `0`
cocycle given by a morphism of inverse systems `T.tower ⟶ W.tower`. -/
def towerHomHomologyClass :
    (T.tower ⟶ W.tower) →ₗ[R] (compatibleHomComplex R T W).homology 0 :=
  (compatibleHomologyZeroEquiv R T W).symm.toLinearMap ∘ₗ
    (compatibleCoboundaries R T W).mkQ ∘ₗ (towerHomEquivCompatibleCocycles R T W).toLinearMap

/-- Under `compatibleHomologyZeroEquiv`, the class of a morphism of inverse systems is the
class of its degree `0` cocycle. -/
lemma compatibleHomologyZeroEquiv_towerHomHomologyClass (α : T.tower ⟶ W.tower) :
    compatibleHomologyZeroEquiv R T W (towerHomHomologyClass R T W α) =
      Submodule.Quotient.mk (towerHomEquivCompatibleCocycles R T W α) :=
  (compatibleHomologyZeroEquiv R T W).apply_symm_apply _

/-- The class of a morphism of inverse systems is the cohomology class of any degree `0`
cycle whose image in the degree `0` cochains is the family of `0`-cochains of the
components of the morphism. -/
lemma towerHomHomologyClass_eq_homologyπ (α : T.tower ⟶ W.tower)
    (x : (compatibleHomComplex R T W).cycles 0)
    (hx : ∀ m : ℕ, (((compatibleHomComplex R T W).iCycles 0).hom x).1 m =
      Cochain.ofHom (α.app (op m))) :
    towerHomHomologyClass R T W α = ((compatibleHomComplex R T W).homologyπ 0).hom x := by
  apply (compatibleHomologyZeroEquiv R T W).injective
  rw [compatibleHomologyZeroEquiv_towerHomHomologyClass, compatibleHomologyZeroEquiv_homologyπ]
  exact congrArg Submodule.Quotient.mk (Subtype.ext (Subtype.ext (funext fun m => (hx m).symm)))

/-- Every degree `0` cohomology class of `compatibleHomComplex R T W` is the class of a
morphism of inverse systems. -/
lemma towerHomHomologyClass_surjective :Function.Surjective (towerHomHomologyClass R T W) :=
  (compatibleHomologyZeroEquiv R T W).symm.surjective.comp
    ((Submodule.mkQ_surjective _).comp (towerHomEquivCompatibleCocycles R T W).surjective)

/-- The kernel of `towerHomHomologyClass` consists of the morphisms whose degree `0`
cocycle is a coboundary. -/
lemma ker_towerHomHomologyClass :
    LinearMap.ker (towerHomHomologyClass R T W) = nullHomotopicTowerHoms R T W := by
  ext α
  rw [LinearMap.mem_ker, ← (compatibleHomologyZeroEquiv R T W).map_eq_zero_iff,
    compatibleHomologyZeroEquiv_towerHomHomologyClass, Submodule.Quotient.mk_eq_zero]
  rfl

/-- A morphism of inverse systems `T.tower ⟶ W.tower` has zero class in the degree `0`
cohomology of `compatibleHomComplex R T W` exactly when it admits a compatible
null-homotopy. -/
theorem towerHomHomologyClass_eq_zero_iff (α : T.tower ⟶ W.tower) :
    towerHomHomologyClass R T W α = 0 ↔ Nonempty (CompatibleNullHomotopy T W α) := by
  rw [← LinearMap.mem_ker, ker_towerHomHomologyClass, mem_nullHomotopicTowerHoms_iff]

/-- The morphisms of inverse systems `T.tower ⟶ W.tower` modulo those admitting a
compatible null-homotopy are the degree `0` cohomology of `compatibleHomComplex R T W`. -/
def towerHomQuotientEquivHomologyZero :
    ((T.tower ⟶ W.tower) ⧸ nullHomotopicTowerHoms R T W) ≃ₗ[R]
      (compatibleHomComplex R T W).homology 0 :=
  (Submodule.Quotient.equiv _ _ (towerHomEquivCompatibleCocycles R T W)
    (Submodule.map_comap_eq_of_surjective (towerHomEquivCompatibleCocycles R T W).surjective
      _)).trans (compatibleHomologyZeroEquiv R T W).symm

/-- `towerHomQuotientEquivHomologyZero` sends the class of `α` to
`towerHomHomologyClass R T W α`. -/
@[simp]
lemma towerHomQuotientEquivHomologyZero_mk (α : T.tower ⟶ W.tower) :
    towerHomQuotientEquivHomologyZero R T W (Submodule.Quotient.mk α) =
      towerHomHomologyClass R T W α :=
  rfl

/-- The morphisms of inverse systems `T.tower ⟶ W.tower` modulo those admitting a
compatible null-homotopy are the degree `0` cohomology of the inverse limit
`homComplexLimit R T W` of the Hom complexes. -/
def towerHomQuotientEquivLimitHomologyZero :
    ((T.tower ⟶ W.tower) ⧸ nullHomotopicTowerHoms R T W) ≃ₗ[R]
      (homComplexLimit R T W).homology 0 :=
  (towerHomQuotientEquivHomologyZero R T W).trans
    ((HomologicalComplex.homologyFunctor (ModuleCat.{v} R) (ComplexShape.up ℤ) 0).mapIso
      (compatibleHomComplexIsoLimit R T W)).toLinearEquiv

/-- `towerHomQuotientEquivLimitHomologyZero` sends the class of `α` to the image of
`towerHomHomologyClass R T W α` under the map on degree `0` cohomology induced by
`compatibleHomComplexIsoLimit`. -/
lemma towerHomQuotientEquivLimitHomologyZero_mk (α : T.tower ⟶ W.tower) :
    towerHomQuotientEquivLimitHomologyZero R T W (Submodule.Quotient.mk α) =
      (HomologicalComplex.homologyMap (compatibleHomComplexIsoLimit R T W).hom 0).hom
        (towerHomHomologyClass R T W α) :=
  rfl

end HomologyZero

end DivisibleSystem

section Smooth

variable (R : Type u) [CommRing R] (G : Type v) [Group G] [TopologicalSpace G] {ℓ : ℕ}

/-- For `ℓ`-divisible systems of cochain complexes of smooth representations, the
morphisms of the inverse systems modulo those admitting a compatible null-homotopy are the
degree `0` cohomology of the inverse limit of the Hom complexes of equivariant maps. -/
abbrev smoothTowerHomQuotientEquivLimitHomologyZero
    (T W : SmoothRepComplexDivisibleSystem.{v, u, w} R G ℓ) :
    ((T.tower ⟶ W.tower) ⧸ DivisibleSystem.nullHomotopicTowerHoms R T W) ≃ₗ[R]
      (DivisibleSystem.homComplexLimit R T W).homology 0 :=
  DivisibleSystem.towerHomQuotientEquivLimitHomologyZero R T W

end Smooth

end Langlands.Cohomology
