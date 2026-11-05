import Langlands.GroupScheme.AffineHopfCoordinates
import Langlands.GroupScheme.AffineCoordinatesFiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

/-! # From Hopf-subalgebra faithful flatness to actual affine group morphisms -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped TensorProduct

namespace Langlands.GroupScheme.AffineHomImageHopfAdapter

/-- The Hopf-subalgebra faithful-flatness input used by the geometric adapter. -/
def HopfSubalgebraFaithfullyFlatStatement (k : Type u) [Field k] : Prop :=
  ∀ (H : Type u) [CommRing H] [HopfAlgebra k H] [Algebra.FiniteType k H]
    (K : Subalgebra k H),
    (∀ x ∈ K, Coalgebra.comul (R := k) x ∈
      Submodule.span k {t : H ⊗[k] H | ∃ a ∈ K, ∃ b ∈ K, t = a ⊗ₜ[k] b}) →
    (∀ x ∈ K, HopfAlgebra.antipode k x ∈ K) →
    Module.FaithfullyFlat K H

section Algebra

variable {R : Type u} [CommRing R] {A B : CommHopfAlgCat.{u} R}

/-- A Hopf-algebra morphism commutes with the antipode, by inverse naturality
on the corresponding algebra cogroups. -/
theorem map_antipode (f : A ⟶ B) (a : A) :
    HopfAlgebra.antipode R (f a) = f (HopfAlgebra.antipode R a) := by
  let φ := ((commHopfAlgCatEquivCogrpCommAlgCat R).functor.map f).unop.hom.hom
  have h := GrpObj.inv_hom φ
  have h' := congrArg (fun z => z.unop.hom) h
  exact DFunLike.congr_fun h' a

/-- The comultiplication of the algebraic range lies in the span of pure
tensors of range elements. -/
theorem comul_mem_range_tensor_span (f : A ⟶ B) (x : B)
    (hx : x ∈ f.hom.toAlgHom.range) :
    Coalgebra.comul (R := R) x ∈
      Submodule.span R {t : B ⊗[R] B |
        ∃ a ∈ f.hom.toAlgHom.range, ∃ b ∈ f.hom.toAlgHom.range,
          t = a ⊗ₜ[R] b} := by
  obtain ⟨a, rfl⟩ := hx
  change Coalgebra.comul (R := R) (f.hom a) ∈ _
  rw [← CoalgHomClass.map_comp_comul_apply f.hom a]
  induction Coalgebra.comul (R := R) a using TensorProduct.inductionOn with
  | tmul a b =>
      exact Submodule.subset_span ⟨f a, ⟨a, rfl⟩, f b, ⟨b, rfl⟩, rfl⟩
  | add a b ha hb =>
      simpa only [map_add] using Submodule.add_mem _ ha hb

/-- The algebraic range is stable under the antipode. -/
theorem antipode_mem_range (f : A ⟶ B) (x : B)
    (hx : x ∈ f.hom.toAlgHom.range) :
    HopfAlgebra.antipode R x ∈ f.hom.toAlgHom.range := by
  obtain ⟨a, rfl⟩ := hx
  exact ⟨HopfAlgebra.antipode R a, (map_antipode f a).symm⟩

end Algebra

section Field

variable {k : Type u} [Field k]

/-- An injective morphism of finite-type commutative Hopf algebras is faithfully
flat, conditional on faithful flatness over Hopf subalgebras. -/
theorem faithfullyFlat_of_injective
    (hff : HopfSubalgebraFaithfullyFlatStatement k)
    {A B : CommHopfAlgCat.{u} k} [Algebra.FiniteType k B]
    (f : A ⟶ B) (hf : Function.Injective f) :
    f.hom.toAlgHom.toRingHom.FaithfullyFlat := by
  let K := f.hom.toAlgHom.range
  have hK : Module.FaithfullyFlat K B :=
    hff B K (comul_mem_range_tensor_span f) (antipode_mem_range f)
  have hval : K.val.toRingHom.FaithfullyFlat :=
    RingHom.faithfullyFlat_algebraMap_iff.mpr hK
  have hr : f.hom.toAlgHom.rangeRestrict.toRingHom.FaithfullyFlat :=
    RingHom.FaithfullyFlat.of_bijective
      ⟨fun _ _ h => hf (congrArg Subtype.val h), f.hom.toAlgHom.rangeRestrict_surjective⟩
  exact RingHom.FaithfullyFlat.stableUnderComposition _ _ hr hval

variable {G H : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]

local instance : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
local instance : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom

/-- The underlying scheme isomorphism of the chosen Hopf-coordinate
group-scheme isomorphism. -/
def coordinateSchemeIso (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] :
    Spec (CommRingCat.of (AffineCoordinates.hopfAlgebra G)) ≅ G.X.left :=
  (Over.forget _).mapIso ((Grp.forget _).mapIso (AffineCoordinates.hopfSpecIso G))

/-- The contravariant Hopf-algebra morphism attached to an actual affine group
homomorphism, using the chosen Hopf-coordinate isomorphisms. -/
def pullback (f : G ⟶ H) :
    AffineCoordinates.hopfAlgebra H ⟶ AffineCoordinates.hopfAlgebra G :=
  (hopfSpec.fullyFaithful.preimage
    ((AffineCoordinates.hopfSpecIso G).hom ≫ f ≫
      (AffineCoordinates.hopfSpecIso H).inv)).unop

/-- Taking spectrum of the chosen coordinate pullback recovers the original
map up to the actual group-scheme coordinate isomorphisms. -/
theorem spec_map_pullback (f : G ⟶ H) :
    Spec.map (CommRingCat.ofHom (pullback f).hom.toAlgHom.toRingHom) =
      (coordinateSchemeIso G).hom ≫ f.hom.hom.left ≫
        (coordinateSchemeIso H).inv := by
  have h := hopfSpec.fullyFaithful.map_preimage
    ((AffineCoordinates.hopfSpecIso G).hom ≫ f ≫
      (AffineCoordinates.hopfSpecIso H).inv)
  exact congrArg (fun g => g.hom.hom.left) h

/-- Scheme-theoretic dominance gives injectivity of the chosen Hopf-coordinate
pullback. No reducedness assumption is needed. -/
theorem pullback_injective (f : G ⟶ H)
    [IsSchemeTheoreticallyDominant f.hom.hom.left] :
    Function.Injective (pullback f) := by
  let ψ := CommRingCat.ofHom (pullback f).hom.toAlgHom.toRingHom
  have : IsSchemeTheoreticallyDominant (Spec.map ψ) := by
    rw [show Spec.map ψ = _ from spec_map_pullback f]
    infer_instance
  have happ : Function.Injective (Spec.map ψ).appTop := (Spec.map ψ).app_injective ⊤
  have hψeq : ψ = (Scheme.ΓSpecIso _).inv ≫ (Spec.map ψ).appTop ≫
      (Scheme.ΓSpecIso _).hom := by
    rw [Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
  have hinj : Function.Injective ψ.hom := by
    rw [hψeq, CommRingCat.hom_comp, CommRingCat.hom_comp, RingHom.coe_comp, RingHom.coe_comp]
    exact (Scheme.ΓSpecIso _).commRingCatIsoToRingEquiv.injective.comp
      (happ.comp (Scheme.ΓSpecIso _).symm.commRingCatIsoToRingEquiv.injective)
  exact hinj

/-- A schematically dominant map from an affine finite-type group scheme is
flat and scheme-surjective, conditional only on Hopf-subalgebra faithful
flatness over the base field. -/
theorem flat_and_surjective
    (hff : HopfSubalgebraFaithfullyFlatStatement k)
    [LocallyOfFiniteType G.X.hom] (f : G ⟶ H)
    [IsSchemeTheoreticallyDominant f.hom.hom.left] :
    Flat f.hom.hom.left ∧ Surjective f.hom.hom.left := by
  have : Algebra.FiniteType k (AffineCoordinates.hopfAlgebra G) :=
    AffineCoordinates.algebraFiniteType G
  have hψ := faithfullyFlat_of_injective hff (pullback f) (pullback_injective f)
  obtain ⟨hf, hs⟩ := (flat_and_surjective_SpecMap_iff
    (CommRingCat.ofHom (pullback f).hom.toAlgHom.toRingHom)).mpr hψ
  have hfac : f.hom.hom.left =
      (coordinateSchemeIso G).inv ≫
        Spec.map (CommRingCat.ofHom (pullback f).hom.toAlgHom.toRingHom) ≫
          (coordinateSchemeIso H).hom := by
    rw [spec_map_pullback f]
    simp
  rw [hfac]
  constructor <;> infer_instance

end Field

end Langlands.GroupScheme.AffineHomImageHopfAdapter
