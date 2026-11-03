import Langlands.GroupScheme.Reductive.Semisimple
import Langlands.AbelianScheme.Kernel
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-! # Actual adjoint quotient interfaces -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section General
variable {S : Scheme.{u}} {G H : GroupScheme S}

/-- A group-scheme homomorphism kills the entire scheme-theoretic centre. -/
def KillsCenter (f : G ⟶ H) : Prop :=
  ∀ (T : Over S) (x : T ⟶ G.X), x ∈ (center G).carrier T → x ≫ f.hom.hom = 1

/-- An actual scheme morphism is invariant under right translation by every central
point, on every test scheme over the base. -/
def IsInvariantUnderCenter {Y : Over S} (f : G.X ⟶ Y) : Prop :=
  ∀ (T : Over S) (x z : T ⟶ G.X), z ∈ (center G).carrier T →
    (x * z) ≫ f = x ≫ f

/-- Killing the centre makes a homomorphism invariant under its right translations. -/
theorem KillsCenter.isInvariantUnderCenter {f : G ⟶ H} (hf : KillsCenter f) :
    IsInvariantUnderCenter f.hom.hom := by
  intro T x z hz
  rw [MonObj.mul_comp, hf T z hz, mul_one]

end General

section Field
variable {k : Type u} [Field k]
variable {G A A' : GroupScheme (Spec (CommRingCat.of k))}

/-- An actual adjoint quotient: an fppf homomorphism to an adjoint group with
full centre as its actual kernel and the scheme and group quotient universal properties.
No finiteness hypothesis is imposed on this quotient morphism. -/
structure IsAdjointQuotient (q : G ⟶ A) : Prop where
  isConnectedReductive : IsConnectedReductive G
  isAdjoint : IsAdjoint A
  flat : Flat q.hom.hom.left
  surjective : Surjective q.hom.hom.left
  locallyOfFinitePresentation : LocallyOfFinitePresentation q.hom.hom.left
  kernelCenter : IsSchemeTheoreticCenter (kernelι q)
  groupUniversal : ∀ (H : GroupScheme (Spec (CommRingCat.of k))) (f : G ⟶ H),
    KillsCenter f → ∃! g : A ⟶ H, q ≫ g = f
  schemeUniversal : ∀ (Y : Over (Spec (CommRingCat.of k))) (f : G.X ⟶ Y),
    IsInvariantUnderCenter f → ∃! g : A.X ⟶ Y, q.hom.hom ≫ g = f

namespace IsAdjointQuotient

variable {q : G ⟶ A} (hq : IsAdjointQuotient q)

include hq

/-- The range functor of the actual kernel is exactly the full centre. -/
theorem kernel_range_eq_center : SubgroupFunctor.range (kernelι q) = center G :=
  hq.kernelCenter.2

/-- A point is central exactly when its image in the actual quotient is the identity. -/
theorem mem_center_iff_comp_eq_one (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ G.X) :
    x ∈ (center G).carrier T ↔ x ≫ q.hom.hom = 1 := by
  constructor
  · intro hx
    rw [← hq.kernel_range_eq_center] at hx
    obtain ⟨y, rfl⟩ := hx
    exact (kernelPointsEquiv q T y).property
  · intro hx
    rw [← hq.kernel_range_eq_center]
    refine ⟨(kernelPointsEquiv q T).symm ⟨x, hx⟩, ?_⟩
    exact congrArg Subtype.val ((kernelPointsEquiv q T).apply_symm_apply ⟨x, hx⟩)

/-- The quotient kills the entire centre, with arbitrary tests. -/
theorem killsCenter : KillsCenter q :=
  fun T x hx => (hq.mem_center_iff_comp_eq_one T x).1 hx

/-- Points of the actual kernel are canonically the points of the full centre. -/
def kernelCenterPointsEquiv (T : Over (Spec (CommRingCat.of k))) :
    (T ⟶ (kernel q).X) ≃* (center G).carrier T :=
  hq.kernelCenter.isRepresentedBy.pointsEquiv T

/-- The kernel-centre identification retains the actual inclusion into the source. -/
theorem kernelCenterPointsEquiv_val {T : Over (Spec (CommRingCat.of k))}
    (x : T ⟶ (kernel q).X) :
    (hq.kernelCenterPointsEquiv T x : T ⟶ G.X) = x ≫ (kernelι q).hom.hom := rfl

/-- The identification is natural under every morphism of test schemes. -/
theorem kernelCenterPointsEquiv_naturality
    {T T' : Over (Spec (CommRingCat.of k))} (a : T' ⟶ T) (x : T ⟶ (kernel q).X) :
    (hq.kernelCenterPointsEquiv T' (a ≫ x) : T' ⟶ G.X) =
      a ≫ (hq.kernelCenterPointsEquiv T x : T ⟶ G.X) :=
  Category.assoc _ _ _

/-- Any supplied actual centre representative is canonically isomorphic to the kernel. -/
def centerKernelIso {Z : GroupScheme (Spec (CommRingCat.of k))} {z : Z ⟶ G}
    (hz : IsSchemeTheoreticCenter z) : Z ≅ kernel q :=
  hz.isRepresentedBy.isoOfIsRepresentedBy hq.kernelCenter.isRepresentedBy

/-- The centre-kernel isomorphism commutes with the actual inclusions into the source. -/
theorem centerKernelIso_hom_comp {Z : GroupScheme (Spec (CommRingCat.of k))} {z : Z ⟶ G}
    (hz : IsSchemeTheoreticCenter z) : (hq.centerKernelIso hz).hom ≫ kernelι q = z :=
  hz.isRepresentedBy.isoOfIsRepresentedBy_hom_comp hq.kernelCenter.isRepresentedBy

/-- The universal factorization of a homomorphism killing the full centre. -/
def desc {H : GroupScheme (Spec (CommRingCat.of k))} (f : G ⟶ H) (hf : KillsCenter f) :
    A ⟶ H :=
  (hq.groupUniversal H f hf).choose

/-- The descended homomorphism composes to the original map. -/
theorem comp_desc {H : GroupScheme (Spec (CommRingCat.of k))}
    (f : G ⟶ H) (hf : KillsCenter f) : q ≫ hq.desc f hf = f :=
  (hq.groupUniversal H f hf).choose_spec.1

/-- Equality of maps from the quotient can be tested after the quotient homomorphism. -/
theorem hom_ext {H : GroupScheme (Spec (CommRingCat.of k))} {f g : A ⟶ H}
    (h : q ≫ f = q ≫ g) : f = g := by
  have hk : KillsCenter (q ≫ g) := by
    intro T x hx
    change x ≫ (q.hom.hom ≫ g.hom.hom) = 1
    rw [← Category.assoc, hq.killsCenter T x hx, MonObj.one_comp]
  obtain ⟨l, _, hl⟩ := hq.groupUniversal H (q ≫ g) hk
  exact (hl f h).trans (hl g rfl).symm

/-- Two actual adjoint quotient interfaces are uniquely isomorphic over the source. -/
def quotientIso {q' : G ⟶ A'} (hq' : IsAdjointQuotient q') : A ≅ A' where
  hom := hq.desc q' hq'.killsCenter
  inv := hq'.desc q hq.killsCenter
  hom_inv_id := by
    apply hq.hom_ext
    rw [← Category.assoc, hq.comp_desc, hq'.comp_desc, Category.comp_id]
  inv_hom_id := by
    apply hq'.hom_ext
    rw [← Category.assoc, hq'.comp_desc, hq.comp_desc, Category.comp_id]

/-- The canonical comparison respects the given quotient homomorphisms. -/
theorem comp_quotientIso_hom {q' : G ⟶ A'} (hq' : IsAdjointQuotient q') :
    q ≫ (hq.quotientIso hq').hom = q' :=
  hq.comp_desc q' hq'.killsCenter

end IsAdjointQuotient
end Field
end Langlands.GroupScheme
