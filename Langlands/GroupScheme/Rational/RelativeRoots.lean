import Langlands.GroupScheme.Rational.SplitTorus
import Langlands.GroupScheme.Rational.TorusCentralizer
import Langlands.GroupScheme.Torus.Maximal
import Langlands.LinearAlgebra.RationalSpan

/-! # Relative roots, the relative Weyl group and generic cocharacters -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj
open Langlands.LinearAlgebra.RationalSpan

namespace Langlands.GroupScheme

/-! ### Closed subgroups are monomorphisms -/

/-- The underlying morphism of schemes of a closed subgroup is a monomorphism. -/
theorem IsClosedSubgroup.mono {S : Scheme.{u}} {H G : GroupScheme S} {i : H ⟶ G}
    (hi : IsClosedSubgroup i) : Mono i.hom.hom.left :=
  haveI : IsClosedImmersion i.hom.hom.left := hi
  inferInstance

/-! ### Torus centralizer and centralizer points -/

/-- At the base scheme the whole-torus centralizer is the subgroup of points centralizing the
torus. -/
theorem torusCentralizer_carrier_base {S : Scheme.{u}} {T : CommGroupScheme S} {G : GroupScheme S}
    (i : T.toGrp ⟶ G) : (torusCentralizer i).carrier (Over.mk (𝟙 S)) = centralizerPoints i :=
  Subgroup.ext fun g => (mem_torusCentralizer_base_iff i g).trans (mem_centralizerPoints i).symm

/-! ### The centralizer points are normal in the normalizer points -/

section Normal

variable {S : Scheme.{u}} {T : CommGroupScheme S} {G : GroupScheme S} (i : T.toGrp ⟶ G)

/-- Conjugating a point centralizing `i` by a point normalizing `i` gives a point
centralizing `i`. -/
theorem conj_mem_centralizerPoints {n z : Over.mk (𝟙 S) ⟶ G.X} (hn : n ∈ normalizerPoints i)
    (hz : z ∈ centralizerPoints i) : n * z * n⁻¹ ∈ centralizerPoints i := by
  obtain ⟨σ, hσ⟩ := hn
  have h := (hσ.mul hz).mul hσ.inv
  rw [Iso.refl_trans, Iso.symm_self_id] at h
  exact h

instance normal_centralizerPoints_subgroupOf :
    ((centralizerPoints i).subgroupOf (normalizerPoints i)).Normal :=
  ⟨fun z hz n => by
    rw [Subgroup.mem_subgroupOf] at hz ⊢
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    exact conj_mem_centralizerPoints i n.2 hz⟩

end Normal

variable {k : Type u} [Field k] {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}

/-- The underlying morphism of schemes of a split subtorus is a monomorphism. -/
theorem IsSplitSubtorus.mono {i : T.toGrp ⟶ G} (hi : IsSplitSubtorus i) : Mono i.hom.hom.left :=
  hi.2.mono

/-! ### Relative roots -/

section Roots

variable [IsAffineHom G.X.hom]

/-- The relative roots (`k`-roots) of a homomorphism `i : T ⟶ G`, meant for a split subtorus:
the published roots of `T` in `G`, the nonzero characters of `T` with a nonzero weight space in
the Lie algebra of `G` under the adjoint action. -/
def relativeRoots (i : T.toGrp ⟶ G) : Set (characterLattice T) :=
  roots i

theorem mem_relativeRoots {i : T.toGrp ⟶ G} {χ : characterLattice T} :
    χ ∈ relativeRoots i ↔ χ ≠ 0 ∧ weightSpace i χ ≠ ⊥ :=
  Iff.rfl

theorem relativeRoots_eq_roots (i : T.toGrp ⟶ G) : relativeRoots i = roots i :=
  rfl

end Roots

/-! ### Anisotropic groups -/

section Anisotropic

variable {i : T.toGrp ⟶ G}

/-- In an anisotropic group every character of a split subtorus is zero. -/
theorem IsAnisotropic.eq_zero_of_isSplitSubtorus (hG : IsAnisotropic G) (hi : IsSplitSubtorus i)
    (χ : characterLattice T) : χ = 0 :=
  haveI := hG.subsingleton_character hi
  Subsingleton.elim χ 0

/-- In an anisotropic group the character lattice of a split subtorus is the zero subgroup. -/
theorem IsAnisotropic.top_eq_bot_of_isSplitSubtorus (hG : IsAnisotropic G)
    (hi : IsSplitSubtorus i) : (⊤ : AddSubgroup (characterLattice T)) = ⊥ :=
  eq_bot_iff.2 fun χ _ => (AddSubgroup.mem_bot).2 (hG.eq_zero_of_isSplitSubtorus hi χ)

/-- In an anisotropic group a split subtorus has no roots. -/
theorem IsAnisotropic.roots_eq_empty [IsAffineHom G.X.hom] (hG : IsAnisotropic G)
    (hi : IsSplitSubtorus i) : roots i = ∅ :=
  Set.eq_empty_iff_forall_notMem.mpr fun χ hχ => hχ.1 (hG.eq_zero_of_isSplitSubtorus hi χ)

/-- In an anisotropic group a split subtorus has no relative roots. -/
theorem IsAnisotropic.relativeRoots_eq_empty [IsAffineHom G.X.hom] (hG : IsAnisotropic G)
    (hi : IsSplitSubtorus i) : relativeRoots i = ∅ :=
  hG.roots_eq_empty hi

end Anisotropic

/-! ### The relative Weyl group -/

/-- The relative Weyl group `N(k)/Z(k)`: the normalizer points of `i` modulo the centralizer
points of `i`. -/
abbrev relativeWeylGroup (i : T.toGrp ⟶ G) : Type u :=
  normalizerPoints i ⧸ (centralizerPoints i).subgroupOf (normalizerPoints i)

/-! ### The span of the relative roots and the Weyl action on it -/

/-- The `ℚ`-span of the image of the relative roots in `ℚ ⊗[ℤ] X*(T)`. -/
def relativeRootSpan [IsAffineHom G.X.hom] (i : T.toGrp ⟶ G) :
    Submodule ℚ (ℚ ⊗[ℤ] characterLattice T) :=
  ratSpan (relativeRoots i)

section WeylAction

variable (i : T.toGrp ⟶ G) [Mono i.hom.hom.left]

/-- Points centralizing `i` act trivially on the characters. -/
theorem weylAction_eq_one_of_mem_centralizerPoints {n : normalizerPoints i}
    (hn : (n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) ∈ centralizerPoints i) :
    weylAction i n = 1 := by
  apply LinearEquiv.ext
  intro χ
  rw [weylAction_eq i hn χ]
  exact Category.id_comp χ

theorem centralizerPoints_subgroupOf_le_ker :
    (centralizerPoints i).subgroupOf (normalizerPoints i) ≤ (weylAction i).ker :=
  fun _ hn => weylAction_eq_one_of_mem_centralizerPoints i hn

variable [IsAffineHom G.X.hom]

/-- The Weyl action preserves the relative roots. -/
theorem weylAction_mapsTo_relativeRoots (n : normalizerPoints i) :
    Set.MapsTo (weylAction i n) (relativeRoots i) (relativeRoots i) :=
  fun χ hχ => (weylAction_mem_roots_iff n χ).2 hχ

theorem weylAction_image_relativeRoots (n : normalizerPoints i) :
    weylAction i n '' relativeRoots i = relativeRoots i :=
  image_eq_of_mapsTo (weylAction i) (weylAction_mapsTo_relativeRoots i) n

/-- The `ℚ`-linear extension of the Weyl action of a normalizing point maps the span of the
relative roots onto itself. -/
theorem map_relativeRootSpan (n : normalizerPoints i) :
    (relativeRootSpan i).map (ratAut (weylAction i n) :
      (ℚ ⊗[ℤ] characterLattice T) →ₗ[ℚ] (ℚ ⊗[ℤ] characterLattice T)) = relativeRootSpan i := by
  rw [relativeRootSpan, map_ratSpan, weylAction_image_relativeRoots]

/-- The action of the relative Weyl group on the span of the relative roots, induced by the Weyl
action of the normalizer points on the characters. -/
def relativeWeylAction : relativeWeylGroup i →* (relativeRootSpan i ≃ₗ[ℚ] relativeRootSpan i) :=
  QuotientGroup.lift _ (spanAut (weylAction i) (relativeRoots i)
    (weylAction_mapsTo_relativeRoots i)) fun _ hz =>
      spanAut_eq_one_of_eq_one _ _ _ (weylAction_eq_one_of_mem_centralizerPoints i hz)

theorem relativeWeylAction_mk (n : normalizerPoints i) :
    relativeWeylAction i (QuotientGroup.mk n) =
      spanAut (weylAction i) (relativeRoots i) (weylAction_mapsTo_relativeRoots i) n :=
  rfl

theorem coe_relativeWeylAction_mk_apply (n : normalizerPoints i) (x : relativeRootSpan i) :
    (relativeWeylAction i (QuotientGroup.mk n) x : ℚ ⊗[ℤ] characterLattice T) =
      ratAut (weylAction i n) x :=
  rfl

theorem relativeWeylAction_mk_toRat (n : normalizerPoints i) {α : characterLattice T}
    (hα : α ∈ relativeRoots i) :
    relativeWeylAction i (QuotientGroup.mk n) ⟨toRat α, toRat_mem_ratSpan hα⟩ =
      ⟨toRat (weylAction i n α), toRat_mem_ratSpan (weylAction_mapsTo_relativeRoots i n hα)⟩ :=
  rfl

end WeylAction

/-! ### Generic cocharacters -/

/-- A cocharacter `ν` of `T` is generic for `i` when it pairs nontrivially with every relative
root. -/
def IsGenericCocharacter [IsAffineHom G.X.hom] (i : T.toGrp ⟶ G) (ν : cocharacterLattice T) :
    Prop :=
  ∀ α ∈ relativeRoots i, latticePairing T α ν ≠ 0

theorem isGenericCocharacter_iff [IsAffineHom G.X.hom] {i : T.toGrp ⟶ G}
    {ν : cocharacterLattice T} :
    IsGenericCocharacter i ν ↔ ∀ α ∈ relativeRoots i, latticePairing T α ν ≠ 0 :=
  Iff.rfl

end Langlands.GroupScheme
