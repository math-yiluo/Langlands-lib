import Langlands.GroupScheme.Reductive.ArtinianCentrality
import Langlands.GroupScheme.Reductive.CentralKernelNoetherianModel

/-! # Global kernel centrality from finite flat Artinian tests -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace Langlands.GroupScheme.NoetherianKernelCentrality

open Descent.FiberCentralityCoefficients

/-- The focused local input: a finite flat kernel over a local Artinian ring
with central canonical residue kernels is central. This remains a hypothesis. -/
def FiniteFlatArtinianKernelCentralityStatement : Prop :=
  ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsArtinianRing A]
    (G H : GroupScheme (Spec (CommRingCat.of A))),
    IsReductive G → IsReductive H → ∀ (f : G ⟶ H),
      LocallyQuasiFinite f.hom.hom.left → Flat f.hom.hom.left →
      Surjective f.hom.hom.left → IsFinite (kernel f).X.hom →
      (∀ p : Spec (CommRingCat.of A), IsCentral (kernelι
        ((baseChange ((Spec (CommRingCat.of A)).fromSpecResidueField p)).map f))) →
      IsCentral (kernelι f)

/-- Arbitrary affine base change preserves centrality of every actual
canonical residue kernel of a homomorphism between reductive groups. -/
theorem central_kernel_fibres_baseChange
    {R : Type u} [CommRing R]
    {G H : GroupScheme (Spec (CommRingCat.of R))}
    (hG : IsReductive G) (hH : IsReductive H) (f : G ⟶ H)
    (hc : ∀ p : Spec (CommRingCat.of R), IsCentral (kernelι
      ((baseChange ((Spec (CommRingCat.of R)).fromSpecResidueField p)).map f)))
    (A : Type u) [CommRing A]
    (b : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of R)) :
    ∀ p : Spec (CommRingCat.of A), IsCentral (kernelι
      ((baseChange ((Spec (CommRingCat.of A)).fromSpecResidueField p)).map
        ((baseChange b).map f))) := by
  let := hG.isAffineHom
  let := hH.isAffineHom
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : IsAffineHom (kernel f).X.hom := by
    rw [← (kernelι f).hom.hom.w]
    infer_instance
  have : IsAffine (kernel f).X.left := isAffine_of_isAffineHom (kernel f).X.hom
  let : Algebra R A := (Spec.preimage b).hom.toAlgebra
  have hb : Spec.algebraMap R A = b := by
    change Spec.map (CommRingCat.ofHom (Spec.preimage b).hom) = b
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  apply (centralFiberLocus_kernel_eq_univ_iff _).1
  rw [← centralFiberLocus_kernel_baseChange b f, ← hb]
  change centralFiberLocus ((baseChange
    (Spec.map (CommRingCat.ofHom (algebraMap R A)))).map (kernelι f)) = Set.univ
  rw [centralFiberLocus_baseChange A (kernelι f),
    (centralFiberLocus_kernel_eq_univ_iff f).2 hc]
  exact Set.preimage_univ

/-- Over noetherian affine bases the local input suffices. Every Artinian test
kernel is finite by quasi-finiteness and affineness over an Artinian base. -/
theorem isCentral_kernel_of_noetherian
    (ha : FiniteFlatArtinianKernelCentralityStatement.{u})
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {G H : GroupScheme (Spec (CommRingCat.of R))}
    (hG : IsReductive G) (hH : IsReductive H) (f : G ⟶ H)
    (hq : LocallyQuasiFinite f.hom.hom.left) (hf : Flat f.hom.hom.left)
    (hs : Surjective f.hom.hom.left)
    (hc : ∀ p : Spec (CommRingCat.of R), IsCentral (kernelι
      ((baseChange ((Spec (CommRingCat.of R)).fromSpecResidueField p)).map f))) :
    IsCentral (kernelι f) := by
  let := hG.smooth
  let := hG.isAffineHom
  let := hH.isAffineHom
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : LocallyOfFiniteType (kernel f).X.hom := by
    rw [← (kernelι f).hom.hom.w]
    infer_instance
  have : IsLocallyNoetherian G.X.left :=
    LocallyOfFiniteType.isLocallyNoetherian G.X.hom
  have : IsLocallyNoetherian ((kernel f).X ⊗ G.X).left := by
    change IsLocallyNoetherian (pullback (kernel f).X.hom G.X.hom)
    infer_instance
  apply ArtinianCentrality.isCentral_of_artinian_baseChange (kernelι f)
  intro A _ _ _ b
  let fA := (baseChange b).map f
  have hGA := hG.baseChange b
  have hHA := hH.baseChange b
  let := hGA.isAffineHom
  let := hHA.isAffineHom
  have hqA : LocallyQuasiFinite fA.hom.hom.left :=
    MorphismProperty.of_isPullback (baseChange_map_isPullback b f).flip hq
  have hfA : Flat fA.hom.hom.left :=
    MorphismProperty.of_isPullback (baseChange_map_isPullback b f).flip hf
  have hsA : Surjective fA.hom.hom.left :=
    MorphismProperty.of_isPullback (baseChange_map_isPullback b f).flip hs
  have : IsAffineHom (kernel fA).X.hom := by
    rw [← (kernelι fA).hom.hom.w]
    infer_instance
  have : LocallyQuasiFinite (kernel fA).X.hom :=
    MorphismProperty.of_isPullback (kernel_isPullback_scheme fA) hqA
  have hkA : IsFinite (kernel fA).X.hom :=
    IsFinite.of_locallyQuasiFinite (kernel fA).X.hom
  apply (KernelInfinitesimalCentrality.isCentral_kernel_baseChange_iff b f).1
  exact ha A _ _ hGA hHA fA hqA hfA hsA hkA
    (central_kernel_fibres_baseChange hG hH f hc A b)

/-- Noetherian approximation preserving actual central residue kernels extends
the preceding result to every affine base, without noetherian assumptions. -/
theorem isCentral_kernel_of_affine
    (ha : FiniteFlatArtinianKernelCentralityStatement.{u})
    {A : Type u} [CommRing A]
    {G H : GroupScheme (Spec (CommRingCat.of A))}
    (hG : IsReductive G) (hH : IsReductive H) (f : G ⟶ H)
    (hq : LocallyQuasiFinite f.hom.hom.left) (hf : Flat f.hom.hom.left)
    (hs : Surjective f.hom.hom.left)
    (hc : ∀ p : Spec (CommRingCat.of A), IsCentral (kernelι
      ((baseChange ((Spec (CommRingCat.of A)).fromSpecResidueField p)).map f))) :
    IsCentral (kernelι f) := by
  let M := centralKernelNoetherianModel hG hH f hq hf hs hc
  let := M.noetherian
  have hM := isCentral_kernel_of_noetherian ha M.source_reductive M.target_reductive
    M.hom M.quasiFinite M.flat M.surjective M.centralFibres
  have hMb := hM.baseChange (Spec.algebraMap M.coefficients A)
  have hMK := (KernelInfinitesimalCentrality.isCentral_kernel_baseChange_iff _ M.hom).2 hMb
  apply (HopfFiberCentralityResidue.isCentral_iff_of_iso_square (kernelι f) _
    (kernelSquareIso f _ M.sourceIso M.targetIso M.recovery.symm) M.sourceIso
    (kernelSquareIso_hom_ι f _ M.sourceIso M.targetIso M.recovery.symm).symm).2
  exact hMK

/-- The actual kernel over an arbitrary affine base, bundled as commutative
using the focused local Artinian input. -/
def centralKernelOfArtinianInput
    (ha : FiniteFlatArtinianKernelCentralityStatement.{u})
    {A : Type u} [CommRing A]
    {G H : GroupScheme (Spec (CommRingCat.of A))}
    (hG : IsReductive G) (hH : IsReductive H) (f : G ⟶ H)
    (hq : LocallyQuasiFinite f.hom.hom.left) (hf : Flat f.hom.hom.left)
    (hs : Surjective f.hom.hom.left)
    (hc : ∀ p : Spec (CommRingCat.of A), IsCentral (kernelι
      ((baseChange ((Spec (CommRingCat.of A)).fromSpecResidueField p)).map f))) :
    CommGroupScheme (Spec (CommRingCat.of A)) :=
  (isCentral_kernel_of_affine ha hG hH f hq hf hs hc).commGroupScheme

@[simp]
theorem centralKernelOfArtinianInput_toGrp
    (ha : FiniteFlatArtinianKernelCentralityStatement.{u})
    {A : Type u} [CommRing A]
    {G H : GroupScheme (Spec (CommRingCat.of A))}
    (hG : IsReductive G) (hH : IsReductive H) (f : G ⟶ H)
    (hq : LocallyQuasiFinite f.hom.hom.left) (hf : Flat f.hom.hom.left)
    (hs : Surjective f.hom.hom.left)
    (hc : ∀ p : Spec (CommRingCat.of A), IsCentral (kernelι
      ((baseChange ((Spec (CommRingCat.of A)).fromSpecResidueField p)).map f))) :
    (centralKernelOfArtinianInput ha hG hH f hq hf hs hc).toGrp = kernel f := rfl

end Langlands.GroupScheme.NoetherianKernelCentrality
