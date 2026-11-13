import Langlands.GroupScheme.Derived.PerfectQuotientImage
import Langlands.GroupScheme.Derived.Functoriality
import Langlands.GroupScheme.Derived.CentralIntersectionProof
import Langlands.GroupScheme.Derived.SemisimplePerfectProof
import Langlands.GroupScheme.CentralIsogeny.ProjectionCentralIsogeny
import Langlands.GroupScheme.CentralIsogeny.FiniteKernelQuotient
import Langlands.GroupScheme.CentralIsogeny.PerfectComposition
import Langlands.GroupScheme.Rational.LeviFactorization
import Langlands.GroupScheme.SimplyConnected.DerivedCoverProof
import Langlands.GroupScheme.Rational.SimplyConnectedCentralizerProductProof

/-!
# Derived subgroups under a surjection with central kernel

Let `f : G → G'` be a surjective homomorphism of connected reductive groups over a field whose
scheme-theoretic kernel is central, and let `d : D → G`, `d' : D' → G'` be the derived subgroups.
The induced homomorphism `f_D : D → D'` (`IsDerivedSubgroup.map`) is a central isogeny.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k] {G G' D D' : GroupScheme (Spec (CommRingCat.of k))}
  {d : D ⟶ G} {d' : D' ⟶ G'}

namespace IsDerivedSubgroup

variable (hd : IsDerivedSubgroup d) (hd' : IsDerivedSubgroup d') (f : G ⟶ G')

include hd hd'

/-- A point of the kernel of `f_D` maps into the kernel of `f`. -/
theorem comp_map_eq_one_iff {T : Over (Spec (CommRingCat.of k))} (x : T ⟶ D.X) :
    x ≫ (hd.map hd' f).hom.hom = 1 ↔ (x ≫ d.hom.hom) ≫ f.hom.hom = 1 := by
  have hcomp : (hd.map hd' f).hom.hom ≫ d'.hom.hom = d.hom.hom ≫ f.hom.hom := by
    rw [← Grp.comp_hom_hom, ← Grp.comp_hom_hom, map_comp]
  have : Mono d'.hom.hom := hd'.isRepresentedBy.1
  constructor
  · intro hx
    rw [Category.assoc, ← hcomp, ← Category.assoc, hx, MonObj.one_comp]
  · intro hx
    apply (cancel_mono d'.hom.hom).mp
    rw [Category.assoc, hcomp, ← Category.assoc, hx, MonObj.one_comp]

/-- The kernel of `f_D` is central when the kernel of `f` is. -/
theorem isCentral_kernelι_map (hf : IsCentral (kernelι f)) :
    IsCentral (kernelι (hd.map hd' f)) := by
  have : Mono d.hom.hom := hd.isRepresentedBy.1
  apply IsCentral.of_comp (j := d) this
  intro T x
  apply (isCentral_kernelι_iff f).mp hf
  have hx : (x ≫ (kernelι (hd.map hd' f)).hom.hom) ≫ (hd.map hd' f).hom.hom = 1 :=
    (mem_range_kernelι_iff _ _).mp ⟨x, rfl⟩
  rw [Grp.comp_hom_hom, ← Category.assoc]
  exact (comp_map_eq_one_iff hd hd' f _).mp hx

/-- The kernel of `f_D` is finite: it lies in the finite central intersection of `D` with the
centre of `G`. -/
theorem isFinite_kernel_map (hG : IsConnectedReductive G) (hG' : IsConnectedReductive G')
    (hf : IsCentral (kernelι f)) :
    IsFinite (kernel (hd.map hd' f)).X.hom := by
  have : IsAffineHom G.X.hom := hG.isAffineHom
  have : LocallyOfFiniteType G.X.hom := by
    have := hG.smooth
    infer_instance
  obtain ⟨C, c, hcc, hcr, hfin⟩ := derivedCentralIntersectionFiniteness k G D d hG hd
  have : IsClosedImmersion c.hom.hom.left := hcc
  have hrep : ((center G).comap d).IsRepresentedBy c := ⟨Over.mono_of_mono_left _, hcr⟩
  have hle : SubgroupFunctor.range (kernelι (hd.map hd' f)) ≤ (center G).comap d := by
    rintro T _ ⟨x, rfl⟩
    apply (isCentral_kernelι_iff f).mp hf
    have hx : (x ≫ (kernelι (hd.map hd' f)).hom.hom) ≫ (hd.map hd' f).hom.hom = 1 :=
      (mem_range_kernelι_iff _ _).mp ⟨x, rfl⟩
    exact (comp_map_eq_one_iff hd hd' f _).mp hx
  let a := hrep.factorHom (kernelι (hd.map hd' f)) hle
  have ha : a ≫ c = kernelι (hd.map hd' f) := hrep.factorHom_comp _ hle
  have : IsAffineHom D.X.hom := by
    have : IsClosedImmersion d.hom.hom.left := hd.1
    rw [← Over.w d.hom.hom]
    infer_instance
  have : IsClosedImmersion (kernelι (hd.map hd' f)).hom.hom.left := by
    have : IsAffineHom D'.X.hom := by
      have : IsClosedImmersion d'.hom.hom.left := hd'.1
      have : IsAffineHom G'.X.hom := hG'.isAffineHom
      rw [← Over.w d'.hom.hom]
      infer_instance
    infer_instance
  have : IsClosedImmersion a.hom.hom.left := by
    have : IsClosedImmersion (a.hom.hom.left ≫ c.hom.hom.left) := by
      rw [← Over.comp_left, ← Grp.comp_hom_hom, ha]
      infer_instance
    exact IsClosedImmersion.of_comp_isClosedImmersion a.hom.hom.left c.hom.hom.left
  rw [← Over.w a.hom.hom]
  infer_instance

/-- `f_D : D → D'` is surjective: the derived subgroup of `G'` lies in the closed image of `D`. -/
theorem surjective_map (hG : IsConnectedReductive G) (hG' : IsConnectedReductive G')
    [Surjective f.hom.hom.left] : Surjective (hd.map hd' f).hom.hom.left := by
  have : Smooth G.X.hom := hG.smooth
  have : IsAffineHom G.X.hom := hG.isAffineHom
  have : ConnectedSpace G.X.left := hG.connectedSpace
  have : Smooth G'.X.hom := hG'.smooth
  have : IsAffineHom G'.X.hom := hG'.isAffineHom
  have : Smooth D.X.hom := hd.smooth_of_connected hG.smooth hG.isAffineHom hG.connectedSpace
  have : ConnectedSpace D.X.left := derivedSubgroupConnectedness k G D d hd inferInstance
  have : IsClosedImmersion d.hom.hom.left := hd.1
  have : IsClosedImmersion d'.hom.hom.left := hd'.1
  have : IsAffineHom D.X.hom := by
    rw [← Over.w d.hom.hom]
    infer_instance
  have : QuasiCompact f.hom.hom.left := by
    have : QuasiCompact (f.hom.hom.left ≫ G'.X.hom) := by
      rw [Over.w]
      infer_instance
    exact QuasiCompact.of_comp f.hom.hom.left G'.X.hom
  have : Flat f.hom.hom.left := flat_of_surjective f
  obtain ⟨C, inc, fac, hinc, hfac, -, hsurj, -⟩ := HomImage.exists_image (d ≫ f)
  have hcomm := PerfectQuotientImage.containsCommutators_range_of_factor d f inc fac
    hd.containsCommutators hinc hfac
  have hle : derivedSubgroup G' ≤ SubgroupFunctor.range inc :=
    derivedSubgroup_le_range inc hinc hcomm
  have : IsClosedImmersion inc.hom.hom.left := hinc
  have hrep : (SubgroupFunctor.range inc).IsRepresentedBy inc := ⟨Over.mono_of_mono_left _, rfl⟩
  have hle' : SubgroupFunctor.range d' ≤ SubgroupFunctor.range inc := by
    rw [hd'.2]
    exact hle
  let a := hrep.factorHom d' hle'
  have ha : a ≫ inc = d' := hrep.factorHom_comp _ hle'
  have hfa : hd.map hd' f ≫ a = fac :=
    hrep.hom_ext (by rw [Category.assoc, ha, map_comp, hfac])
  have hinj : Function.Injective a.hom.hom.left := by
    intro x y hxy
    apply (d'.hom.hom.left).isClosedEmbedding.injective
    rw [← ha, Grp.comp_hom_hom, Over.comp_left, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hxy]
  refine ⟨fun y => ?_⟩
  obtain ⟨x, hx⟩ := hsurj.surj (a.hom.hom.left y)
  refine ⟨x, hinj ?_⟩
  rw [← Scheme.Hom.comp_apply, ← Over.comp_left, ← Grp.comp_hom_hom, hfa, hx]

/-- `f_D : D → D'` is a central isogeny. -/
theorem isCentralIsogeny_map (hG : IsConnectedReductive G) (hG' : IsConnectedReductive G')
    [Surjective f.hom.hom.left] (hf : IsCentral (kernelι f)) :
    IsCentralIsogeny (hd.map hd' f) := by
  have : Smooth G.X.hom := hG.smooth
  have : IsAffineHom G.X.hom := hG.isAffineHom
  have : IsAffineHom G'.X.hom := hG'.isAffineHom
  have : IsClosedImmersion d.hom.hom.left := hd.1
  have : IsClosedImmersion d'.hom.hom.left := hd'.1
  have : IsAffineHom D.X.hom := by
    rw [← Over.w d.hom.hom]
    infer_instance
  have : IsAffineHom D'.X.hom := by
    rw [← Over.w d'.hom.hom]
    infer_instance
  have : Smooth D.X.hom := hd.smooth_of_connected hG.smooth hG.isAffineHom hG.connectedSpace
  have : Smooth D'.X.hom :=
    hd'.smooth_of_connected hG'.smooth hG'.isAffineHom hG'.connectedSpace
  have hsurj := surjective_map hd hd' f hG hG'
  have : QuasiCompact (hd.map hd' f).hom.hom.left := by
    have : QuasiCompact ((hd.map hd' f).hom.hom.left ≫ D'.X.hom) := by
      rw [Over.w]
      infer_instance
    exact QuasiCompact.of_comp _ D'.X.hom
  have hflat : Flat (hd.map hd' f).hom.hom.left := flat_of_surjective (hd.map hd' f)
  have : IsFinite (kernel (hd.map hd' f)).X.hom := isFinite_kernel_map hd hd' f hG hG' hf
  have hfin : IsFinite (hd.map hd' f).hom.hom.left := isFinite_of_finite_kernel (hd.map hd' f)
  have : LocallyOfFiniteType (hd.map hd' f).hom.hom.left := by
    have : LocallyOfFiniteType ((hd.map hd' f).hom.hom.left ≫ D'.X.hom) := by
      rw [Over.w]
      infer_instance
    exact locallyOfFiniteType_of_comp _ D'.X.hom
  have : IsLocallyNoetherian D'.X.left := LocallyOfFiniteType.isLocallyNoetherian D'.X.hom
  have hlfp : LocallyOfFinitePresentation (hd.map hd' f).hom.hom.left :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr inferInstance
  exact ⟨⟨hfin, hflat, hsurj⟩, hlfp, isCentral_kernelι_map hd hd' f hf⟩

end IsDerivedSubgroup

/-- KP Fact 2.6.22 along a surjection `f : G → G'` with central kernel: every `g' ∈ G'(k)` is a
product `f(g) · z'` with `g ∈ G(k)` and `z'` in the centralizer `Z'` of a maximal split torus of
`G'`. The simply connected cover `π' : C' → D'` of the derived subgroup of `G'` factors through
the central isogeny `C → D → D'` from the simply connected cover of the derived subgroup of `G`,
and Fact 2.6.22 for `G'` applies. -/
theorem exists_eq_map_mul_centralizer_of_centralSurjection
    {S' : CommGroupScheme (Spec (CommRingCat.of k))} {G G' Z' : GroupScheme (Spec (CommRingCat.of k))}
    (hG : IsConnectedReductive G) (hG' : IsConnectedReductive G') (f : G ⟶ G')
    [Surjective f.hom.hom.left] (hf : IsCentral (kernelι f))
    {i' : S'.toGrp ⟶ G'} (hi' : IsMaximalSplitTorus i') {j' : Z' ⟶ G'}
    (hj' : (torusCentralizer i').IsRepresentedBy j') (g' : rationalPoints G') :
    ∃ (g : rationalPoints G) (z : rationalPoints Z'),
      g' = rationalPoints.map f g * rationalPoints.map j' z := by
  obtain ⟨D, C, d, π, hcov⟩ := simplyConnectedDerivedCoverExistence k G hG
  obtain ⟨D', C', d', π', hcov'⟩ := simplyConnectedDerivedCoverExistence k G' hG'
  have hfD := hcov.isDerivedSubgroup.isCentralIsogeny_map hcov'.isDerivedSubgroup f hG hG' hf
  have hCss : IsSemisimple C := hcov.isSimplyConnectedCover.isSimplyConnected.isSemisimple
  have hq : IsCentralIsogeny (π ≫ hcov.isDerivedSubgroup.map hcov'.isDerivedSubgroup f) :=
    IsCentralIsogeny.comp_of_derivedSubgroup_eq_top (semisimplePerfect k C hCss)
      hcov.isSimplyConnectedCover.isCentralIsogeny hfD
  obtain ⟨a, ha, -⟩ := hcov'.isSimplyConnectedCover.universal C _ hCss hq
  obtain ⟨c', z, hg'⟩ :=
    simplyConnectedCentralizerProduct k S' G' Z' C' D' i' j' d' π' hcov' hi' hj' g'
  refine ⟨rationalPoints.map (a ≫ π ≫ d) c', z, ?_⟩
  have hcomp : π' ≫ d' = (a ≫ π ≫ d) ≫ f := by
    rw [← ha, Category.assoc, Category.assoc, IsDerivedSubgroup.map_comp, Category.assoc,
      Category.assoc]
  rw [hg', hcomp]
  congr 1

end Langlands.GroupScheme
