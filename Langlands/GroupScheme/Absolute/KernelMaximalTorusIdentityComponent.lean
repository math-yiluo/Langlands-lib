import Langlands.GroupScheme.Absolute.KernelMaximalTorusUnipotent
import Langlands.GroupScheme.IdentityComponent
import Langlands.GroupScheme.Torus.SplitReflection
import Langlands.GroupScheme.Torus.FiniteGaloisSplittingProof

/-! # Unipotent kernels from a maximal torus of a possibly disconnected group -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Conjugacy of homomorphisms is preserved by composing with a homomorphism. -/
theorem HomConjugate.comp {S : Scheme.{u}} {A B C : GroupScheme S} {χ ψ : A ⟶ B}
    (h : HomConjugate χ ψ) (j : B ⟶ C) : HomConjugate (χ ≫ j) (ψ ≫ j) := by
  obtain ⟨g, hg⟩ := h
  refine ⟨g ≫ j.hom.hom, ?_⟩
  rw [Category.assoc, ← innerIso_hom_comp, ← Category.assoc, hg]

variable {k : Type u} [Field k] [IsAlgClosed k]
  {G H : GroupScheme (Spec (CommRingCat.of k))}

/-- Over an algebraically closed field, a maximal torus of a smooth affine group factors through
the identity component as a maximal torus of the identity component. -/
theorem exists_isMaximalTorus_identityComponent [Smooth G.X.hom] [IsAffineHom G.X.hom]
    {S : CommGroupScheme (Spec (CommRingCat.of k))} {s : S.toGrp ⟶ G}
    (hs : IsMaximalTorus s) :
    ∃ s₀ : S.toGrp ⟶ identityComponent G,
      s₀ ≫ identityComponentι G = s ∧ IsMaximalTorus s₀ := by
  have hsplit : IsSplitTorus S.toGrp :=
    hs.1.isSplitTorus_of_finiteGaloisSplitting torusFiniteGaloisSplitting
  obtain ⟨s₀, hs₀, -⟩ := IdentityComponent.existsUnique_factor_of_isSplitTorus G hsplit s
  have hι := IdentityComponent.isClosedSubgroup_identityComponentι G
  refine ⟨s₀, hs₀, hs.1, IsClosedSubgroup.of_comp hι (hs₀ ▸ hs.2.1), ?_⟩
  intro T' i' f hT' hi' hf
  have : IsClosedImmersion i'.hom.hom.left := hi'
  have : IsClosedImmersion (identityComponentι G).hom.hom.left := hι
  have hcl : IsClosedSubgroup (i' ≫ identityComponentι G) := by
    change IsClosedImmersion (i'.hom.hom.left ≫ (identityComponentι G).hom.hom.left)
    infer_instance
  exact hs.2.2 T' (i' ≫ identityComponentι G) f hT' hcl
    (by rw [← Category.assoc, hf, hs₀])

/-- In a smooth affine group over an algebraically closed field, connected or not, every
cocharacter is conjugate to one factoring through a given maximal torus: both factor through
the identity component, where maximal tori are conjugate. -/
theorem exists_homConjugate_of_isMaximalTorus_identityComponent
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    {S : CommGroupScheme (Spec (CommRingCat.of k))} {s : S.toGrp ⟶ G}
    (hs : IsMaximalTorus s) (z : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G) :
    ∃ w : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ S.toGrp, HomConjugate z (w ≫ s) := by
  obtain ⟨s₀, hs₀, hmax⟩ := exists_isMaximalTorus_identityComponent hs
  have : ConnectedSpace (Gm (Spec (CommRingCat.of k))).toGrp.X.left :=
    isSplitTorus_gm.connectedSpace
  obtain ⟨w, hw⟩ := exists_homConjugate_of_isMaximalTorus hmax
    (IdentityComponent.factor G z)
  refine ⟨w, ?_⟩
  have h := hw.comp (identityComponentι G)
  rwa [IdentityComponent.factor_identityComponentι, Category.assoc, hs₀] at h

/-- **Unipotent kernel from injectivity on a maximal torus, without connectedness of the
source.** Let `q : G → H` be a homomorphism of group schemes over an algebraically closed
field, with `G` smooth and affine, and let `s : S → G` be a maximal torus such that no nonzero
cocharacter of `S` is killed by `s ≫ q`. If the kernel of `q` is smooth, affine and connected,
it is unipotent. -/
theorem isUnipotent_kernel_of_isMaximalTorus_of_smooth (q : G ⟶ H)
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    [Smooth (kernel q).X.hom] [IsAffineHom (kernel q).X.hom]
    [ConnectedSpace (kernel q).X.left]
    {S : CommGroupScheme (Spec (CommRingCat.of k))} {s : S.toGrp ⟶ G}
    (hs : IsMaximalTorus s)
    (hinj : ∀ w : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ S.toGrp, w ≫ s ≫ q = 0 → w = 0) :
    IsUnipotent (kernel q) :=
  isUnipotent_kernel_of_homConjugate q
    (exists_homConjugate_of_isMaximalTorus_identityComponent hs) hinj

end Langlands.GroupScheme
