import Langlands.AlgebraicGeometry.FiniteEtale.MonoEpiConservativeStatements
import Langlands.AlgebraicGeometry.FiniteEtale.GeometricFiniteLimitsCoproductsProof
import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
import Mathlib.CategoryTheory.Limits.Constructions.EpiMono

open CategoryTheory CategoryTheory.Limits

universe u

set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.FiniteEtale

open _root_.AlgebraicGeometry

/-- A monomorphism of finite étale covers has a complementary finite étale cover. -/
theorem geometricMonomorphismComplements {S : Scheme.{u}} [ConnectedSpace S]
    [IsLocallyNoetherian S] {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) (hfin : ∀ Y : Cover S, Finite (Fiber s Y)) :
    GeometricMonomorphismComplements s hfin := by
  classical
  intro X Y i hi
  have hfe : finiteEtale i.hom.left :=
    finiteEtale.of_postcomp (W' := finiteEtale) i.hom.left Y.obj.hom Y.property (by
      rw [Over.w]
      exact X.property)
  have : IsFinite i.hom.left := hfe.1
  have : Etale i.hom.left := hfe.2
  have : Mono i.hom := preserves_mono_of_preservesLimit (inclusion S) i
  have : Mono i.hom.left := inferInstance
  have : IsClosedImmersion i.hom.left :=
    (IsClosedImmersion.iff_isFinite_and_mono _).mpr ⟨inferInstance, inferInstance⟩
  have : IsOpenImmersion i.hom.left := IsOpenImmersion.of_flat_of_mono _
  let U : Y.obj.left.Opens :=
    ⟨(Set.range i.hom.left)ᶜ, i.hom.left.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  have : IsClosedImmersion U.ι :=
    IsClosedImmersion.of_isPreimmersion _ (by
      simpa [U] using (IsOpenImmersion.isOpen_range i.hom.left).isClosed_compl)
  let Z : Cover S := cover (U.ι ≫ Y.obj.hom)
  let v : Z ⟶ Y := ⟨Over.homMk U.ι⟩
  refine ⟨Z, v, ?_⟩
  have hc : Nonempty (IsColimit (BinaryCofan.mk i.hom.left U.ι)) :=
    nonempty_isColimit_binaryCofanMk_of_isCompl _ _ (by
      rw [Scheme.Opens.opensRange_ι, isCompl_iff, disjoint_iff, codisjoint_iff]
      constructor <;> ext x <;> simp [U])
  have hmap : IsColimit ((coverToScheme S).mapCocone (BinaryCofan.mk i v)) :=
    (isColimitMapCoconeBinaryCofanEquiv _ _ _).symm hc.some
  exact ⟨isColimitOfReflects (coverToScheme S) hmap⟩

end Langlands.AlgebraicGeometry.FiniteEtale
