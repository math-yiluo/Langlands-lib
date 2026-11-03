import Langlands.AlgebraicGeometry.CotangentDualNumber
import Langlands.GroupScheme.Lie.GroupAlgebraCoordinates
import Langlands.GroupScheme.Lie.ZeroTangentTrivialityStatement
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.RingTheory.Ideal.IdempotentFG
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Topology.Connected.Clopen

/-! # Connected affine groups with zero tangent space -/

noncomputable section

universe u v

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Lie

set_option backward.isDefEq.respectTransparency false

open Langlands.AlgebraicGeometry

/-- An augmented Noetherian algebra with connected spectrum and no nonconstant
augmented dual-number lift is the base field. -/
theorem augmentation_bijective_of_trivial_lifts
    {k : Type u} [Field k] {A : Type v} [CommRing A] [Algebra k A]
    [IsNoetherianRing A] [PreconnectedSpace (PrimeSpectrum A)]
    (r : A →ₐ[k] k)
    (h : ∀ f : A →ₐ[k] DualNumber k,
      (TrivSqZeroExt.fstHom k k k).comp f = r →
      f = (TrivSqZeroExt.inlAlgHom k k k).comp r) :
    Function.Bijective r := by
  let I := RingHom.ker r.toRingHom
  have hzero (ell : I.Cotangent →ₗ[k] k) : ell = 0 :=
    (cotangentDualNumberLift_eq_constant_iff r ell).mp
      (h _ (cotangentDualNumberLift_projection r ell))
  have hdual : Subsingleton (Module.Dual k I.Cotangent) :=
    ⟨fun f g => (hzero f).trans (hzero g).symm⟩
  have hcot : Subsingleton I.Cotangent :=
    (Module.subsingleton_dual_iff k).mp hdual
  obtain ⟨e, he, hI⟩ :=
    (I.isIdempotentElem_iff_of_fg (IsNoetherian.noetherian I)).mp
      (I.cotangent_subsingleton_iff.mp hcot)
  have heI : e ∈ I := by
    rw [hI]
    exact Submodule.mem_span_singleton_self e
  let q : PrimeSpectrum A := ⟨I, RingHom.ker_isPrime r.toRingHom⟩
  have hcl : IsClopen (PrimeSpectrum.basicOpen e : Set (PrimeSpectrum A)) :=
    PrimeSpectrum.isClopen_iff.mpr ⟨e, he, rfl⟩
  have hempty : (PrimeSpectrum.basicOpen e : Set (PrimeSpectrum A)) = ∅ := by
    rcases isClopen_iff.mp hcl with hempty | hfull
    · exact hempty
    · have hq : q ∈ PrimeSpectrum.basicOpen e := by
        change q ∈ (PrimeSpectrum.basicOpen e : Set (PrimeSpectrum A))
        rw [hfull]
        trivial
      exact False.elim (hq heI)
  have he0 : e = 0 := by
    apply PrimeSpectrum.basicOpen_injOn_isIdempotentElem he
      (show IsIdempotentElem (0 : A) from mul_zero _)
    apply TopologicalSpace.Opens.ext
    simpa using hempty
  have hI0 : I = ⊥ := by simp [hI, he0]
  refine ⟨(RingHom.injective_iff_ker_eq_bot r.toRingHom).mpr hI0, ?_⟩
  intro c
  exact ⟨algebraMap k A c, by simp⟩

attribute [local instance] coordinateOriginAlgebra

variable {k : Type u} [Field k]
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    [ConnectedSpace G.X.left] [Subsingleton (lieKernel G k)]

/-- A connected affine group of finite type with trivial tangent kernel is
the base scheme. -/
theorem isIso_structure_of_subsingleton_lieKernel : IsIso G.X.hom := by
  let C := coordinateAlgebra G
  let r := coordinateOrigin G
  have : Algebra.FiniteType k C := coordinateAlgebraFiniteType G
  have : IsNoetherianRing C := Algebra.FiniteType.isNoetherianRing k C
  have : IsIso ((coordinateIso G).hom.left) :=
    inferInstanceAs (IsIso (((Over.forget _).mapIso (coordinateIso G)).hom))
  have : ConnectedSpace (PrimeSpectrum C) :=
    ((coordinateIso G).hom.left).homeomorph.connectedSpace_iff.mpr inferInstance
  have hr : Function.Bijective r := by
    apply augmentation_bijective_of_trivial_lifts
    intro f hf
    let y : {f : C →ₐ[k] DualNumber k //
        (TrivSqZeroExt.fstHom k k k).comp f =
          IsScalarTower.toAlgHom k C k} :=
      ⟨f, hf⟩
    have hy : y = kernelCoordinates G (1 : lieKernel G k) := by
      rw [← (kernelCoordinates G).apply_symm_apply y]
      congr 1
      exact Subsingleton.elim _ _
    have hy' := congrArg Subtype.val hy
    change f = pointCoordinates G (1 : AffinePoints G (DualNumber k)) at hy'
    rw [pointCoordinates_one] at hy'
    exact hy'
  have hb : Function.Bijective (algebraMap k C) := by
    refine ⟨(show Function.LeftInverse r (algebraMap k C) from r.commutes).injective, ?_⟩
    intro c
    refine ⟨r c, hr.injective ?_⟩
    exact r.commutes (r c)
  have : IsIso (CommRingCat.ofHom (algebraMap k C)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hb
  have hcomp : IsIso ((coordinateIso G).hom.left ≫ G.X.hom) := by
    rw [Over.w]
    change IsIso (Spec.map (CommRingCat.ofHom (algebraMap k C)))
    infer_instance
  have := hcomp
  exact IsIso.of_isIso_comp_left (coordinateIso G).hom.left G.X.hom

/-- Triviality holds over every test scheme, including nonreduced tests. -/
theorem points_eq_one_of_subsingleton_lieKernel
    (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ G.X) : x = 1 := by
  have := isIso_structure_of_subsingleton_lieKernel G
  apply Over.OverMorphism.ext
  apply (cancel_mono G.X.hom).mp
  simp only [Over.w]

end Langlands.GroupScheme.Lie

namespace Langlands.GroupScheme

/-- The exact zero-tangent triviality statement, at every universe. -/
theorem zeroTangentTriviality : ZeroTangentTrivialityStatement.{u} := by
  intro k _ G _ _ _ _
  exact ⟨Lie.isIso_structure_of_subsingleton_lieKernel G,
    Lie.points_eq_one_of_subsingleton_lieKernel G⟩

end Langlands.GroupScheme
