import Langlands.GroupScheme.Descent.GaloisInvariantClosedSubgroups
import Langlands.GroupScheme.Descent.AffineFppfQuotient
import Langlands.GroupScheme.CentralIsogeny.Transport

/-! # Descent of central isogenies with Galois-invariant full kernels -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.Descent

/-- An actual affine central-isogeny target over the original base, with an
isomorphism recovering the supplied target and its exact quotient arrow. -/
structure CentralIsogenyRecovery {B S : Scheme.{u}} (b : S ⟶ B)
    {G : GroupScheme B} {Q : GroupScheme S}
    (q : (GroupScheme.baseChange b).obj G ⟶ Q) where
  obj : GroupScheme B
  hom : G ⟶ obj
  isAffine : IsAffine obj.X.left
  isCentralIsogeny : IsCentralIsogeny hom
  iso : (GroupScheme.baseChange b).obj obj ≅ Q
  hom_comp : (GroupScheme.baseChange b).map hom ≫ iso.hom = q

variable {k K : Type u} [Field k] [Field K] [Algebra k K] [IsGalois k K]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    {Q : GroupScheme (Spec (CommRingCat.of K))} [IsAffine Q.X.left]
    (q : (GroupScheme.baseChange (algebraBaseMap k K)).obj G ⟶ Q)

/-- All-test Galois invariance of the full kernel suffices to descend a
supplied affine central isogeny, including its target and quotient arrow. -/
theorem nonempty_centralIsogenyRecovery_of_galoisInvariant_kernel
    (hq : IsCentralIsogeny q)
    (hinv : ∀ σ : K ≃ₐ[k] K,
      SubgroupFunctor.range (radicalGaloisHom (kernelι q) σ) =
        SubgroupFunctor.range (kernelι q)) :
    Nonempty (CentralIsogenyRecovery (algebraBaseMap k K) q) := by
  have : IsAffineHom Q.X.hom := inferInstance
  have hk : IsClosedSubgroup (kernelι q) :=
    inferInstanceAs (IsClosedImmersion (kernelι q).hom.hom.left)
  obtain ⟨N, i, a, _, hi, ha⟩ :=
    GaloisInvariantClosedSubgroup.exists_descent hk hinv
  have : IsClosedImmersion i.hom.hom.left := hi
  have : Mono i.hom.hom := Over.mono_of_mono_left _
  have : Flat (algebraBaseMap k K) := (fieldExtension_fpqc k K).2.1
  have : Surjective (algebraBaseMap k K) := (fieldExtension_fpqc k K).1
  have : QuasiCompact (algebraBaseMap k K) := (fieldExtension_fpqc k K).2.2
  have : IsFinite q.hom.hom.left := hq.isFinite
  have hquot : RelativeRoot.IsFppfQuotient
      (SubgroupFunctor.range ((GroupScheme.baseChange (algebraBaseMap k K)).map i)) q := by
    refine ⟨hq.flat, hq.surjective, hq.locallyOfFinitePresentation, ?_⟩
    rw [ha, SubgroupFunctor.range_iso_comp]
  obtain ⟨R, r, hR, _, e, he⟩ :=
    exists_affine_fppfQuotient (algebraBaseMap k K) i Q q hquot
  have hr : IsCentralIsogeny ((GroupScheme.baseChange (algebraBaseMap k K)).map r) := by
    apply (isCentralIsogeny_comp_iso_iff _ e).mp
    rw [he]
    exact hq
  exact ⟨{
    obj := R
    hom := r
    isAffine := hR
    isCentralIsogeny := centralIsogenyFpqcReflection _ _ (algebraBaseMap k K) G R r hr
    iso := e
    hom_comp := he
  }⟩

/-- Choose an actual affine central isogeny over the ground field from a
supplied one with Galois-invariant full kernel, retaining exact recovery. -/
def centralIsogenyRecoveryOfGaloisInvariantKernel
    (hq : IsCentralIsogeny q)
    (hinv : ∀ σ : K ≃ₐ[k] K,
      SubgroupFunctor.range (radicalGaloisHom (kernelι q) σ) =
        SubgroupFunctor.range (kernelι q)) :
    CentralIsogenyRecovery (algebraBaseMap k K) q :=
  Classical.choice
    (nonempty_centralIsogenyRecovery_of_galoisInvariant_kernel q hq hinv)

end Langlands.GroupScheme.Descent
