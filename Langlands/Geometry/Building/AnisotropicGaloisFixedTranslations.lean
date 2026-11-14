import Langlands.GroupScheme.Rational.AnisotropicGaloisFixedCharacters
import Langlands.GroupScheme.Rational.RootSupportFiniteness
import Langlands.Geometry.Building.GaloisAffineRootAction
import Langlands.Geometry.Building.AffineIrreducibleChamberTransitivity

/-!
# Galois-fixed translations of the apartment of an anisotropic group

Let `G` be an anisotropic affine group of locally finite type over `k`, let `i : T ⟶ G` be a
closed subgroup, and let `K/k` be a Galois extension, possibly infinite, over which `T` splits.
The coefficient action of `K ≃ₐ[k] K` on the reduced translation space `V(T_K) / V(T_K)^Φ` of the
apartment of `i_K` fixes only the zero vector (`eq_zero_of_forall_galoisTranslationAction_eq`).
For a vector `w` and a root `α`, the sum of the Galois orbit of `α` is a Galois-fixed character
of `T_K`, hence zero because `G` is anisotropic; if the class of `w` is fixed, every root in the
orbit takes the value `α(w)` at `w`, so the orbit size times `α(w)` is zero.

Consequently, for a Galois-stable KP apartment whose affine roots form a nonempty irreducible
affine root system, a chamber stabilized by the Galois action satisfies both chamber-transitivity
conclusions used in the proof of KP Theorem 10.3.1
(`KPApartmentData.chamberTransitivity_of_isAnisotropic`).
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.Geometry.Building

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G)

local notation "b" => algebraBaseMap k K
local notation "T_K" => CategoryTheory.Functor.obj (CommGroupScheme.baseChange b) T
local notation "G_K" => CategoryTheory.Functor.obj (GroupScheme.baseChange b) G
local notation "i_K" => CategoryTheory.Functor.map (GroupScheme.baseChange b) i

private instance extendedAffineHom : IsAffineHom (G_K).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom b)
  infer_instance

private instance extendedLocallyOfFiniteType [LocallyOfFiniteType G.X.hom] :
    LocallyOfFiniteType (G_K).X.hom := by
  change LocallyOfFiniteType (CategoryTheory.Limits.pullback.snd G.X.hom b)
  infer_instance

/-- Evaluation at a fixed real cocharacter is additive in the character. -/
private theorem eval_finset_sum {S : CommGroupScheme (Spec (CommRingCat.of K))} {J : Type*}
    (s : Finset J) (f : J → characterLattice S) (w : RealTorusSpace.V S) :
    RealTorusSpace.eval S (∑ j ∈ s, f j) w = ∑ j ∈ s, RealTorusSpace.eval S (f j) w := by
  let e : characterLattice S →+ ℝ :=
    { toFun := fun χ => RealTorusSpace.eval S χ w
      map_zero' := eval_zero_char w
      map_add' := fun x y => eval_add_char x y w }
  exact map_sum e f s

/-- If the class of `w` in the reduced translation space is fixed by `σ⁻¹`, then the Galois
transport by `σ` of a root takes the same value at `w` as the root itself. -/
theorem eval_galoisRootAction_of_fixed (w : RealTorusSpace.V T_K) (σ : K ≃ₐ[k] K)
    (hv : galoisTranslationAction k K i σ⁻¹
        (Submodule.Quotient.mk w : TranslationSpace (S := T_K) i_K) = Submodule.Quotient.mk w)
    (a : relativeRoots (T := T_K) i_K) :
    RealTorusSpace.eval T_K (galoisRootAction k K i σ a : characterLattice T_K) w =
      RealTorusSpace.eval T_K (a : characterLattice T_K) w := by
  have h1 := RealTorusSpace.eval_galoisCocharacterAction_right k K T σ⁻¹ a.val w
  rw [inv_inv] at h1
  have h3 := congrArg (rootForm (S := T_K) i_K a) hv
  rw [galoisTranslationAction_mk, rootForm_mk, rootForm_mk] at h3
  rw [galoisRootAction_val, ← h1]
  exact h3

/-- The sum of a finite set of roots stable under the Galois action is a Galois-fixed
character. -/
theorem galoisRepresentation_sum_of_stable (O : Finset (relativeRoots (T := T_K) i_K))
    (hO : ∀ σ : K ≃ₐ[k] K, ∀ β ∈ O, galoisRootAction k K i σ β ∈ O) (τ : K ≃ₐ[k] K) :
    characterLattice.galoisRepresentation k K T τ (∑ β ∈ O, (β : characterLattice T_K)) =
      ∑ β ∈ O, (β : characterLattice T_K) := by
  rw [map_sum]
  refine Finset.sum_nbij' (fun β => galoisRootAction k K i τ β)
    (fun β => galoisRootAction k K i τ⁻¹ β) (fun β hβ => hO τ β hβ)
    (fun β hβ => hO τ⁻¹ β hβ) ?_ ?_ (fun β _ => (galoisRootAction_val k K i τ β).symm)
  · intro β _
    rw [← Equiv.Perm.mul_apply, ← map_mul, inv_mul_cancel, map_one, Equiv.Perm.one_apply]
  · intro β _
    rw [← Equiv.Perm.mul_apply, ← map_mul, mul_inv_cancel, map_one, Equiv.Perm.one_apply]

/-- The Galois orbit of a relative root of `i_K`, as a finite set (the relative roots of a
split torus form a finite set). -/
def galoisRootOrbit [LocallyOfFiniteType G.X.hom] (hT : IsSplitTorus (T_K).toGrp)
    (a : relativeRoots (T := T_K) i_K) : Finset (relativeRoots (T := T_K) i_K) :=
  haveI : Finite (relativeRoots (T := T_K) i_K) :=
    (@IsSplitTorus.finite_relativeRoots K _ T_K G_K (extendedAffineHom k K)
      (extendedLocallyOfFiniteType k K) i_K hT).to_subtype
  (Set.toFinite (Set.range fun σ : K ≃ₐ[k] K => galoisRootAction k K i σ a)).toFinset

theorem mem_galoisRootOrbit [LocallyOfFiniteType G.X.hom]
    (hT : IsSplitTorus (T_K).toGrp) (a β : relativeRoots (T := T_K) i_K) :
    β ∈ galoisRootOrbit k K i hT a ↔ ∃ σ : K ≃ₐ[k] K, galoisRootAction k K i σ a = β := by
  unfold galoisRootOrbit
  rw [Set.Finite.mem_toFinset, Set.mem_range]

theorem self_mem_galoisRootOrbit [LocallyOfFiniteType G.X.hom]
    (hT : IsSplitTorus (T_K).toGrp)
    (a : relativeRoots (T := T_K) i_K) : a ∈ galoisRootOrbit k K i hT a :=
  (mem_galoisRootOrbit k K i hT a a).2 ⟨1, by rw [map_one, Equiv.Perm.one_apply]⟩

theorem galoisRootAction_mem_galoisRootOrbit [LocallyOfFiniteType G.X.hom]
    (hT : IsSplitTorus (T_K).toGrp)
    (a : relativeRoots (T := T_K) i_K) (σ : K ≃ₐ[k] K) (β : relativeRoots (T := T_K) i_K)
    (hβ : β ∈ galoisRootOrbit k K i hT a) :
    galoisRootAction k K i σ β ∈ galoisRootOrbit k K i hT a := by
  obtain ⟨τ, rfl⟩ := (mem_galoisRootOrbit k K i hT a β).1 hβ
  exact (mem_galoisRootOrbit k K i hT a _).2 ⟨σ * τ, by rw [map_mul, Equiv.Perm.mul_apply]⟩

/-- For anisotropic `G`, the sum of the Galois orbit of a relative root of `i_K` is zero. -/
theorem sum_galoisRootOrbit_eq_zero [IsGalois k K] [LocallyOfFiniteType G.X.hom]
    (hG : IsAnisotropic G) (hi : IsClosedSubgroup i) (hT : IsSplitTorus (T_K).toGrp)
    (a : relativeRoots (T := T_K) i_K) :
    ∑ β ∈ galoisRootOrbit k K i hT a, (β : characterLattice T_K) = 0 :=
  IsAnisotropic.galoisFixed_character_eq_zero hG hi (isTorus_of_isSplitTorus_baseChange K hT)
    K _ (galoisRepresentation_sum_of_stable k K i _
      (galoisRootAction_mem_galoisRootOrbit k K i hT a))

/-- For anisotropic `G`, every relative root of `i_K` vanishes at a vector whose class in the
reduced translation space is fixed by every `σ : K ≃ₐ[k] K`. -/
theorem eval_eq_zero_of_forall_fixed [IsGalois k K] [LocallyOfFiniteType G.X.hom]
    (hG : IsAnisotropic G) (hi : IsClosedSubgroup i) (hT : IsSplitTorus (T_K).toGrp)
    (w : RealTorusSpace.V T_K)
    (hv : ∀ σ : K ≃ₐ[k] K, galoisTranslationAction k K i σ
        (Submodule.Quotient.mk w : TranslationSpace (S := T_K) i_K) = Submodule.Quotient.mk w)
    (a : relativeRoots (T := T_K) i_K) :
    RealTorusSpace.eval T_K (a : characterLattice T_K) w = 0 := by
  have hval : ∀ β ∈ galoisRootOrbit k K i hT a,
      RealTorusSpace.eval T_K (β : characterLattice T_K) w =
        RealTorusSpace.eval T_K (a : characterLattice T_K) w := by
    intro β hβ
    obtain ⟨σ, rfl⟩ := (mem_galoisRootOrbit k K i hT a β).1 hβ
    exact eval_galoisRootAction_of_fixed k K i w σ (hv σ⁻¹) a
  have h := eval_finset_sum K (galoisRootOrbit k K i hT a)
    (fun β => (β : characterLattice T_K)) w
  rw [Finset.sum_congr rfl hval, Finset.sum_const, nsmul_eq_mul,
    sum_galoisRootOrbit_eq_zero k K i hG hi hT a, eval_zero_char] at h
  have hcard : ((galoisRootOrbit k K i hT a).card : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.2 (Finset.card_pos.2 ⟨a, self_mem_galoisRootOrbit k K i hT a⟩).ne'
  exact (mul_eq_zero.1 h.symm).resolve_left hcard

/-- **Galois-fixed translations vanish for anisotropic groups.** Let `G` be anisotropic and of
locally finite type over `k`, `i : T ⟶ G` a closed subgroup, and `K/k` a Galois extension
over which `T` is split. A vector of the reduced translation space of `i_K` fixed by every
`σ : K ≃ₐ[k] K` is zero. -/
theorem eq_zero_of_forall_galoisTranslationAction_eq [IsGalois k K]
    [LocallyOfFiniteType G.X.hom] (hG : IsAnisotropic G) (hi : IsClosedSubgroup i)
    (hT : IsSplitTorus (T_K).toGrp) (v : TranslationSpace (S := T_K) i_K)
    (hv : ∀ σ : K ≃ₐ[k] K, galoisTranslationAction k K i σ v = v) : v = 0 := by
  obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ v
  rw [Submodule.Quotient.mk_eq_zero, mem_rootAnnihilator]
  intro α hα
  exact eval_eq_zero_of_forall_fixed k K i hG hi hT w hv ⟨α, hα⟩

namespace KPApartmentData

open AffineRootSystem GalleryGeometry

variable [Mono (CategoryTheory.Functor.map
    (GroupScheme.baseChange (algebraBaseMap k K)) i).hom.hom.left]
  {ω : Kˣ → ℝ}
  (D : KPApartmentData
    (S := CategoryTheory.Functor.obj (CommGroupScheme.baseChange (algebraBaseMap k K)) T)
    (CategoryTheory.Functor.map (GroupScheme.baseChange (algebraBaseMap k K)) i) ω)
  (hD : GaloisStable k K i D)

/-- For an arbitrary `ω`, the actual coefficient affine action preserves the actual affine-root
set. (`galoisAffineAction_mem_rootStabilizer` in `GaloisIncidentFacets` is the special case of an
integer valuation.) -/
theorem mem_rootStabilizer_galoisAffineAction (σ : K ≃ₐ[k] K) :
    galoisAffineAction k K i D hD σ ∈ rootStabilizer D.affineRoots := by
  have h : (galoisAffineAction k K i D hD σ)⁻¹ ∈ rootStabilizer D.affineRoots := by
    intro ψ
    exact galoisAffineFunctional_mem_affineRoots_iff k K i D hD σ ψ
  simpa only [inv_inv] using (rootStabilizer D.affineRoots).inv_mem h

/-- **Chamber transitivity for anisotropic groups.** Let `G` be anisotropic and of locally
finite type over `k`, `i : T ⟶ G` a closed subgroup, `K/k` a Galois extension over which `T`
splits, and `D` a Galois-stable KP apartment of `i_K` whose affine roots form a nonempty
irreducible affine root system. If the Galois action stabilizes the chamber of a regular point
`c`, then any simple affine root of that chamber is carried to any other by a root-preserving
affine automorphism, and the chamber Cartan matrix is vertex transitive. -/
theorem chamberTransitivity_of_isAnisotropic [IsGalois k K] [LocallyOfFiniteType G.X.hom]
    (hG : IsAnisotropic G) (hi : IsClosedSubgroup i) (hT : IsSplitTorus (T_K).toGrp)
    (hΨ : IsAffineRootSystemWithRankZero D.affineRoots) {c : D.Apartment}
    [Fintype (simpleAffineRoots D.affineRoots (facet D.affineRoots c))]
    (hirr : IsIrreducibleRoots D.affineRoots) (hc : IsRegular D.affineRoots c)
    (hne : D.affineRoots.Nonempty)
    (hC : ∀ σ : K ≃ₐ[k] K,
      galoisAffineAction k K i D hD σ '' facet D.affineRoots c = facet D.affineRoots c) :
    HasTransitiveSimpleRoots D.affineRoots (facet D.affineRoots c) ∧
      AffineCartan.IsVertexTransitive (chamberCartanMatrix D.affineRoots (facet D.affineRoots c)) :=
  hΨ.chamberTransitivity_of_hom_of_linear hirr hc hne (galoisAffineAction k K i D hD)
    (mem_rootStabilizer_galoisAffineAction k K i D hD) hC
    (fun v hv => eq_zero_of_forall_galoisTranslationAction_eq k K i hG hi hT v hv)

/-- The same conclusion when the regular point `c` itself is fixed by the Galois action: the
action then stabilizes the chamber of `c`. -/
theorem chamberTransitivity_of_isAnisotropic_of_fixed [IsGalois k K]
    [LocallyOfFiniteType G.X.hom]
    (hG : IsAnisotropic G) (hi : IsClosedSubgroup i) (hT : IsSplitTorus (T_K).toGrp)
    (hΨ : IsAffineRootSystemWithRankZero D.affineRoots) {c : D.Apartment}
    [Fintype (simpleAffineRoots D.affineRoots (facet D.affineRoots c))]
    (hirr : IsIrreducibleRoots D.affineRoots) (hc : IsRegular D.affineRoots c)
    (hne : D.affineRoots.Nonempty)
    (hcfix : ∀ σ : K ≃ₐ[k] K, galoisAction k K i D hD σ c = c) :
    HasTransitiveSimpleRoots D.affineRoots (facet D.affineRoots c) ∧
      AffineCartan.IsVertexTransitive
        (chamberCartanMatrix D.affineRoots (facet D.affineRoots c)) := by
  refine chamberTransitivity_of_isAnisotropic k K i D hD hG hi hT hΨ hirr hc hne fun σ => ?_
  have h := image_facet_transportedRoots (galoisAffineAction k K i D hD σ) D.affineRoots c
  rw [transportedRoots_galoisAffineAction, galoisAffineAction_apply, hcfix σ] at h
  exact h

end KPApartmentData

end Langlands.Geometry.Building
