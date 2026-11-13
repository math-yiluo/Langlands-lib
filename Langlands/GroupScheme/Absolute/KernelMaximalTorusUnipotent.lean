import Langlands.GroupScheme.Absolute.NoCocharacterUnipotent
import Langlands.GroupScheme.Absolute.MaximalTorusConjugacyProof
import Langlands.GroupScheme.Rational.MaximalTorusFiniteType
import Langlands.GroupScheme.ConjugacyBaseChange
import Langlands.GroupScheme.Torus.ImageProof

/-! # Unipotent kernels from injectivity on a maximal torus -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section Kernel

variable {S : Scheme.{u}} {G H : GroupScheme S}

/-- The kernel inclusion followed by the homomorphism is trivial. -/
theorem kernelι_comp_eq_zero (q : G ⟶ H) : kernelι q ≫ q = 0 := by
  apply Grp.hom_ext
  rw [Grp.comp_hom_hom, (kernel_isPullback q).w]
  rfl

/-- A homomorphism into the kernel is trivial once its composite with the inclusion is. -/
theorem eq_zero_of_comp_kernelι_eq_zero {J : GroupScheme S} (q : G ⟶ H)
    (z : J ⟶ kernel q) (hz : z ≫ kernelι q = 0) : z = 0 := by
  apply Grp.hom_ext
  apply (cancel_mono (kernelι q).hom.hom).mp
  rw [← Grp.comp_hom_hom, hz, ← Grp.comp_hom_hom, zero_comp]

end Kernel

section Conjugate

variable {S : Scheme.{u}} {G H : GroupScheme S} (q : G ⟶ H)

/-- **Cocharacters killed by a homomorphism, via conjugacy.** Let `q : G → H` and `s : M → G`
be group-scheme homomorphisms over any base. Suppose that every cocharacter of `G` is
conjugate, by a base point of `G`, to a cocharacter factoring through `s`, and that no nonzero
cocharacter of `M` is killed by `s ≫ q`. Then every cocharacter of `G` killed by `q` is zero:
conjugation commutes with `q` up to an inner automorphism of `H`. -/
theorem cocharacter_eq_zero_of_homConjugate {M : GroupScheme S} {s : M ⟶ G}
    (hconj : ∀ z : (Gm S).toGrp ⟶ G, ∃ w : (Gm S).toGrp ⟶ M, HomConjugate z (w ≫ s))
    (hinj : ∀ w : (Gm S).toGrp ⟶ M, w ≫ s ≫ q = 0 → w = 0)
    (z : (Gm S).toGrp ⟶ G) (hz : z ≫ q = 0) : z = 0 := by
  obtain ⟨w, g, hw⟩ := hconj z
  have hws : w ≫ s ≫ q = 0 := by
    rw [← Category.assoc, ← hw, Category.assoc, innerIso_hom_comp, ← Category.assoc, hz,
      zero_comp]
  have hzg : z ≫ (G.innerIso g).hom = 0 := by
    rw [hw, hinj w hws, zero_comp]
  calc z = z ≫ (G.innerIso g).hom ≫ (G.innerIso g).inv := by simp
    _ = 0 := by rw [← Category.assoc, hzg, zero_comp]

/-- The injectivity hypothesis holds when `s ≫ q` is a monomorphism of schemes. -/
theorem cocharacter_injective_of_mono {M : GroupScheme S} {s : M ⟶ G}
    [Mono (s ≫ q).hom.hom] (w : (Gm S).toGrp ⟶ M) (hw : w ≫ s ≫ q = 0) : w = 0 := by
  apply Grp.hom_ext
  apply (cancel_mono (s ≫ q).hom.hom).mp
  rw [← Grp.comp_hom_hom, hw, ← Grp.comp_hom_hom, zero_comp]

end Conjugate

variable {k : Type u} [Field k] [IsAlgClosed k]
  {G H : GroupScheme (Spec (CommRingCat.of k))} (q : G ⟶ H)

/-- **Unipotent kernel from cocharacter conjugacy.** Let `q : G → H` be a homomorphism of
group schemes over an algebraically closed field whose kernel is smooth, affine and connected.
If every cocharacter of `G` is conjugate to one factoring through `s : M → G`, and no nonzero
cocharacter of `M` is killed by `s ≫ q`, then the kernel of `q` is unipotent. -/
theorem isUnipotent_kernel_of_homConjugate
    [Smooth (kernel q).X.hom] [IsAffineHom (kernel q).X.hom]
    [ConnectedSpace (kernel q).X.left]
    {M : GroupScheme (Spec (CommRingCat.of k))} {s : M ⟶ G}
    (hconj : ∀ z : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G,
      ∃ w : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ M, HomConjugate z (w ≫ s))
    (hinj : ∀ w : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ M, w ≫ s ≫ q = 0 → w = 0) :
    IsUnipotent (kernel q) := by
  apply algClosedNoCocharacterUnipotent k (kernel q)
  intro z
  apply eq_zero_of_comp_kernelι_eq_zero q z
  apply cocharacter_eq_zero_of_homConjugate q hconj hinj
  rw [Category.assoc, kernelι_comp_eq_zero, comp_zero]

/-- In a smooth connected affine group over an algebraically closed field, every cocharacter
is conjugate to one factoring through a given maximal torus. The image of a cocharacter is a
closed torus, it lies in a maximal torus, and that maximal torus is conjugate to the given
one. -/
theorem exists_homConjugate_of_isMaximalTorus
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    {S : CommGroupScheme (Spec (CommRingCat.of k))} {s : S.toGrp ⟶ G}
    (hs : IsMaximalTorus s) (z : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G) :
    ∃ w : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ S.toGrp, HomConjugate z (w ≫ s) := by
  obtain ⟨Z, j, p, hZ, hj, hpj⟩ := torusImageClosedTorusStatement k G _
    isSplitTorus_gm.isTorus z
  obtain ⟨M, j', hj', f, hf⟩ := exists_maximalTorus_extension_of_finiteType G j hZ hj
  obtain ⟨g, φ, hg⟩ := maximalTorusConjugacy k G M S j' s hj' hs
  refine ⟨p ≫ f ≫ CommGroupScheme.groupHom φ.hom, g, ?_⟩
  rw [← hpj, ← hf]
  simp only [Category.assoc, hg]

/-- **Unipotent kernel from injectivity on a maximal torus.** Let `q : G → H` be a homomorphism
of group schemes over an algebraically closed field, with `G` smooth, affine and connected, and
let `s : S → G` be a maximal torus such that no nonzero cocharacter of `S` is killed by
`s ≫ q`. If the kernel of `q` is smooth, affine and connected, it is unipotent. -/
theorem isUnipotent_kernel_of_isMaximalTorus
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    [Smooth (kernel q).X.hom] [IsAffineHom (kernel q).X.hom]
    [ConnectedSpace (kernel q).X.left]
    {S : CommGroupScheme (Spec (CommRingCat.of k))} {s : S.toGrp ⟶ G}
    (hs : IsMaximalTorus s)
    (hinj : ∀ w : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ S.toGrp, w ≫ s ≫ q = 0 → w = 0) :
    IsUnipotent (kernel q) :=
  isUnipotent_kernel_of_homConjugate q (exists_homConjugate_of_isMaximalTorus hs) hinj

end Langlands.GroupScheme
