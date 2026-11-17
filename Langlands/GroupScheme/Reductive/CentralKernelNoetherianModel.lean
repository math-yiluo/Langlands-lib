import Langlands.GroupScheme.Descent.FiberCentralityCoefficients
import Langlands.GroupScheme.Reductive.QuasiFiniteNoetherianModelProof
import Langlands.GroupScheme.KernelSquareTransport
import Langlands.GroupScheme.Reductive.KernelInfinitesimalCentrality
import Langlands.GroupScheme.Descent.Data

/-! # Noetherian reductive models retaining central residue kernels -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

namespace Langlands.GroupScheme

open Descent.FiberCentralityCoefficients

/-- The actual kernel comparison identifies the two residue-centrality loci. -/
theorem centralFiberLocus_kernel_baseChange
    {S : Scheme.{u}} {R : CommRingCat.{u}} (b : Spec R ⟶ S)
    {G H : GroupScheme S} (f : G ⟶ H) :
    centralFiberLocus ((baseChange b).map (kernelι f)) =
      centralFiberLocus (kernelι ((baseChange b).map f)) := by
  apply centralFiberLocus_iso_square _ _ (kernelBaseChangeIso b f) (Iso.refl _)
  simpa only [Iso.refl_hom, Category.comp_id] using
    (kernelBaseChangeIso_hom_ι b f).symm

/-- An isomorphism of arrows identifies the loci of their kernel inclusions. -/
theorem centralFiberLocus_kernel_iso_square
    {R : CommRingCat.{u}} {G H G' H' : GroupScheme (Spec R)}
    (f : G ⟶ H) (f' : G' ⟶ H') (eG : G ≅ G') (eH : H ≅ H')
    (w : eG.hom ≫ f' = f ≫ eH.hom) :
    centralFiberLocus (kernelι f) = centralFiberLocus (kernelι f') := by
  apply centralFiberLocus_iso_square _ _ (kernelSquareIso f f' eG eH w) eG
  exact (kernelSquareIso_hom_ι f f' eG eH w).symm

/-- Fullness of the inclusion locus is centrality of every actual residue kernel. -/
theorem centralFiberLocus_kernel_eq_univ_iff
    {R : CommRingCat.{u}} {G H : GroupScheme (Spec R)} (f : G ⟶ H) :
    centralFiberLocus (kernelι f) = Set.univ ↔
      ∀ p : Spec R, IsCentral (kernelι ((baseChange ((Spec R).fromSpecResidueField p)).map f)) := by
  rw [Set.eq_univ_iff_forall]
  exact forall_congr' fun p =>
    (KernelInfinitesimalCentrality.isCentral_kernel_baseChange_iff _ f).symm

private theorem centralModel_spec_comp (R B A : Type u) [CommRing R] [CommRing B]
    [CommRing A] [Algebra R B] [Algebra B A] [Algebra R A] [IsScalarTower R B A] :
    Spec.algebraMap B A ≫ Spec.algebraMap R B = Spec.algebraMap R A := by
  rw [Spec.algebraMap, Spec.algebraMap, Spec.algebraMap,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]

/-- Enlarge the noetherian coefficient ring while retaining the reductive groups,
map properties, and exact recovery of the supplied homomorphism. -/
def NoetherianQuasiFiniteModel.enlarge
    {A : Type u} [CommRing A]
    {G H : GroupScheme (Spec (CommRingCat.of A))} {f : G ⟶ H}
    (M : NoetherianQuasiFiniteModel f) (T : Subalgebra M.coefficients A) (hT : T.FG) :
    NoetherianQuasiFiniteModel f where
  coefficients := T.toSubring
  noetherian := by
    let := M.noetherian
    exact isNoetherianRing_of_fg hT
  source := (baseChange (Spec.algebraMap M.coefficients T)).obj M.source
  target := (baseChange (Spec.algebraMap M.coefficients T)).obj M.target
  source_reductive := M.source_reductive.baseChange _
  target_reductive := M.target_reductive.baseChange _
  hom := (baseChange (Spec.algebraMap M.coefficients T)).map M.hom
  quasiFinite := MorphismProperty.of_isPullback
    (baseChange_map_isPullback (Spec.algebraMap M.coefficients T) M.hom).flip M.quasiFinite
  flat := MorphismProperty.of_isPullback
    (baseChange_map_isPullback (Spec.algebraMap M.coefficients T) M.hom).flip M.flat
  surjective := MorphismProperty.of_isPullback
    (baseChange_map_isPullback (Spec.algebraMap M.coefficients T) M.hom).flip M.surjective
  sourceIso := M.sourceIso ≪≫
    (Descent.pullbackComparison (Spec.algebraMap M.coefficients T) (Spec.algebraMap T A)
      (Spec.algebraMap M.coefficients A) (centralModel_spec_comp M.coefficients T A) M.source).symm
  targetIso := M.targetIso ≪≫
    (Descent.pullbackComparison (Spec.algebraMap M.coefficients T) (Spec.algebraMap T A)
      (Spec.algebraMap M.coefficients A) (centralModel_spec_comp M.coefficients T A) M.target).symm
  recovery := by
    let cG := Descent.pullbackComparison (Spec.algebraMap M.coefficients T)
      (Spec.algebraMap T A) (Spec.algebraMap M.coefficients A)
      (centralModel_spec_comp M.coefficients T A) M.source
    let cH := Descent.pullbackComparison (Spec.algebraMap M.coefficients T)
      (Spec.algebraMap T A) (Spec.algebraMap M.coefficients A)
      (centralModel_spec_comp M.coefficients T A) M.target
    change f ≫ (M.targetIso ≪≫ cH.symm).hom =
      (M.sourceIso ≪≫ cG.symm).hom ≫
        (baseChange (Spec.algebraMap T A)).map
          ((baseChange (Spec.algebraMap M.coefficients T)).map M.hom)
    apply (cancel_mono cH.hom).mp
    have hn : (baseChange (Spec.algebraMap T A)).map
        ((baseChange (Spec.algebraMap M.coefficients T)).map M.hom) ≫ cH.hom =
        cG.hom ≫ (baseChange (Spec.algebraMap M.coefficients A)).map M.hom :=
      Descent.pullbackComparison_naturality _ _ _ _ M.hom
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, hn,
      Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
    exact M.recovery

/-- A noetherian reductive model whose actual kernel is central on every
canonical residue fibre. -/
structure CentralKernelNoetherianModel
    {A : Type u} [CommRing A]
    {G H : GroupScheme (Spec (CommRingCat.of A))} (f : G ⟶ H)
    extends NoetherianQuasiFiniteModel f where
  centralFibres : ∀ p : Spec (CommRingCat.of coefficients),
    IsCentral (kernelι ((baseChange
      ((Spec (CommRingCat.of coefficients)).fromSpecResidueField p)).map hom))

/-- Enlarge a supplied noetherian model to retain centrality of the original
homomorphism's residue kernels. -/
def NoetherianQuasiFiniteModel.centralEnlargement
    {A : Type u} [CommRing A]
    {G H : GroupScheme (Spec (CommRingCat.of A))}
    {f : G ⟶ H} (M : NoetherianQuasiFiniteModel f)
    (hc : ∀ p : Spec (CommRingCat.of A),
      IsCentral (kernelι ((baseChange
        ((Spec (CommRingCat.of A)).fromSpecResidueField p)).map f))) :
    CentralKernelNoetherianModel f := by
  let := M.noetherian
  let := M.source_reductive.isAffineHom
  let := M.target_reductive.isAffineHom
  let := M.source_reductive.smooth
  have : IsAffine M.source.X.left := isAffine_of_isAffineHom M.source.X.hom
  have : IsAffineHom (kernel M.hom).X.hom := by
    rw [← (kernelι M.hom).hom.hom.w]
    infer_instance
  have : IsAffine (kernel M.hom).X.left := isAffine_of_isAffineHom (kernel M.hom).X.hom
  have : LocallyOfFiniteType (kernel M.hom).X.hom := by
    rw [← (kernelι M.hom).hom.hom.w]
    infer_instance
  have hMC : centralFiberLocus
      ((baseChange (Spec.algebraMap M.coefficients A)).map (kernelι M.hom)) = Set.univ := by
    rw [centralFiberLocus_kernel_baseChange]
    change centralFiberLocus (kernelι ((baseChange
      (Spec.map (CommRingCat.ofHom M.coefficients.subtype))).map M.hom)) = Set.univ
    exact (centralFiberLocus_kernel_iso_square f _ M.sourceIso M.targetIso
      M.recovery.symm).symm.trans ((centralFiberLocus_kernel_eq_univ_iff f).2 hc)
  let C := centralFiberCoefficientModel A (kernelι M.hom) hMC ∅
  let E := M.enlarge C.coefficients C.finiteGeneration
  refine { toNoetherianQuasiFiniteModel := E, centralFibres := ?_ }
  apply (centralFiberLocus_kernel_eq_univ_iff E.hom).1
  change centralFiberLocus
    (kernelι ((baseChange (Spec.algebraMap M.coefficients C.coefficients)).map M.hom)) = Set.univ
  rw [← centralFiberLocus_kernel_baseChange]
  exact C.centralFibres

/-- Preserve supplied centrality of every actual residue kernel while choosing
noetherian coefficients for a reductive quasi-finite flat surjection. -/
def centralKernelNoetherianModel
    {A : Type u} [CommRing A]
    {G H : GroupScheme (Spec (CommRingCat.of A))}
    (hG : IsReductive G) (hH : IsReductive H) (f : G ⟶ H)
    (hq : LocallyQuasiFinite f.hom.hom.left) (hf : Flat f.hom.hom.left)
    (hs : Surjective f.hom.hom.left)
    (hc : ∀ p : Spec (CommRingCat.of A),
      IsCentral (kernelι ((baseChange
        ((Spec (CommRingCat.of A)).fromSpecResidueField p)).map f))) :
    CentralKernelNoetherianModel f :=
  (Classical.choice (reductiveQuasiFiniteNoetherianModel A G H hG hH f hq hf hs)).centralEnlargement hc

end Langlands.GroupScheme
