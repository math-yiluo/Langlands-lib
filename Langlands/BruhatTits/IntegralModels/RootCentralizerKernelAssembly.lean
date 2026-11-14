import Langlands.BruhatTits.IntegralModels.RootCentralizerOpenCharts
import Langlands.GroupScheme.KernelOrderedProductOpenChart
import Langlands.GroupScheme.Rational.GenericCocharacter
import Langlands.GroupScheme.Rational.RootSmoothQuotient
import Langlands.GroupScheme.Torus.SmoothQuotientCentralizer
import Langlands.GroupScheme.Unipotent.KernelCoordinateTransport

/-! # Full ambient kernels from root and centralizer kernels -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace Langlands.BruhatTits.IntegralModels.RootCentralizerKernel

section Base

variable {B : Scheme.{u}}

/-- Actual factors together with their inclusions, ordered as the negative
block, the whole centralizer, and the positive block. -/
def chartData {nN nP : ℕ} {N : Fin nN → GroupScheme B}
    {Z : GroupScheme B} {P : Fin nP → GroupScheme B} {G : GroupScheme B}
    (jN : ∀ r, N r ⟶ G) (jZ : Z ⟶ G) (jP : ∀ r, P r ⟶ G) :
    Fin (nN + (nP + 1)) → Σ A : GroupScheme B, A ⟶ G :=
  Fin.addCases (fun r => ⟨N r, jN r⟩)
    (Fin.cases ⟨Z, jZ⟩ (fun r => ⟨P r, jP r⟩))

/-- Monic postcomposition detects smoothness of the full original kernel. -/
theorem smooth_kernel_of_monic_comp {A C D : GroupScheme B}
    (f : A ⟶ C) (l : C ⟶ D) [Mono l.hom.hom]
    (h : Smooth (kernel (f ≫ l)).X.hom) : Smooth (kernel f).X.hom := by
  let : Smooth (kernel (f ≫ l)).X.hom := h
  exact KernelRepresentative.smooth f (kernelι (f ≫ l))
    (range_kernelι_comp_mono f l).symm

/-- Changing a full subgroup representative preserves smoothness of the
full kernel after an arbitrary fixed ambient homomorphism. -/
theorem smooth_kernel_of_representatives
    {G H U V : GroupScheme B} {F : SubgroupFunctor G}
    (q : G ⟶ H) (j : U ⟶ G) (l : V ⟶ G)
    (hj : F.IsRepresentedBy j) (hl : F.IsRepresentedBy l)
    (h : Smooth (kernel (j ≫ q)).X.hom) : Smooth (kernel (l ≫ q)).X.hom := by
  let e := hl.isoOfIsRepresentedBy hj
  let ek := kernelCoordinateIso (j ≫ q) (l ≫ q) e (by
    rw [← Category.assoc, hl.isoOfIsRepresentedBy_hom_comp hj])
  let eo := (Grp.forget (Over B)).mapIso ek
  have : IsIso eo.hom.left := (Over.forget B).map_isIso eo.hom
  let : Smooth ((Grp.forget (Over B)).obj (kernel (j ≫ q))).hom := h
  change Smooth ((Grp.forget (Over B)).obj (kernel (l ≫ q))).hom
  rw [← eo.hom.w]
  infer_instance

end Base

section Field

variable {k : Type u} [Field k] [IsAlgClosed k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G H Z : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [Smooth G.X.hom] [ConnectedSpace G.X.left]
    [IsAffineHom H.X.hom] [Smooth H.X.hom] [ConnectedSpace H.X.left]
    (hS : IsSplitTorus S.toGrp) (i : S.toGrp ⟶ G) (q : G ⟶ H)
    (jZ : Z ⟶ G) (hjZ : (torusCentralizer i).IsRepresentedBy jZ)

include hS hjZ

/-- Rootwise and full-centralizer composite kernels control the full ambient
kernel through compatible actual open multiplication charts. -/
theorem smooth_kernel_of_root_and_centralizer
    (hsub : relativeRoots (i ≫ q) ⊆ relativeRoots i)
    (hdisj : ∀ a ∈ RelativeRoot.indivisibleRoots i,
      ∀ b ∈ RelativeRoot.indivisibleRoots i, a ≠ b →
        Disjoint (RelativeRoot.cyclicTail a 1 : Set (characterLattice S))
          (RelativeRoot.cyclicTail b 1 : Set (characterLattice S)))
    (hroot : ∀ a ∈ relativeRoots i,
      ∀ (U : GroupScheme (Spec (CommRingCat.of k))) (j : U ⟶ G),
        (RelativeRoot.subgroup i a).IsRepresentedBy j →
          Smooth (kernel (j ≫ q)).X.hom)
    (hcenter : Smooth (kernel (jZ ≫ q)).X.hom) :
    Smooth (kernel q).X.hom := by
  classical
  obtain ⟨ν, hν⟩ := hS.exists_genericCocharacter i
  have hνH : IsGenericCocharacter (i ≫ q) ν := fun a ha => hν a (hsub ha)
  obtain ⟨nN, aN, haNi, haN⟩ := RelativeRoot.indivisiblePositiveRootEnumeration
    i (-ν) (hS.finite_relativeRoots i)
  obtain ⟨nP, aP, haPi, haP⟩ := RelativeRoot.indivisiblePositiveRootEnumeration
    i ν (hS.finite_relativeRoots i)
  have hdN : ∀ a ∈ RelativeRoot.indivisiblePositiveRoots i (-ν),
      ∀ b ∈ RelativeRoot.indivisiblePositiveRoots i (-ν), a ≠ b →
        Disjoint (RelativeRoot.cyclicTail a 1 : Set (characterLattice S))
          (RelativeRoot.cyclicTail b 1 : Set (characterLattice S)) :=
    fun a ha b hb => hdisj a ha.1 b hb.1
  have hdP : ∀ a ∈ RelativeRoot.indivisiblePositiveRoots i ν,
      ∀ b ∈ RelativeRoot.indivisiblePositiveRoots i ν, a ≠ b →
        Disjoint (RelativeRoot.cyclicTail a 1 : Set (characterLattice S))
          (RelativeRoot.cyclicTail b 1 : Set (characterLattice S)) :=
    fun a ha b hb => hdisj a ha.1 b hb.1
  let DN := RelativeRoot.dynamicRootProductOfLargerSupport hS i i
    (fun _ h => h) (-ν) nN aN haNi haN hdN
  let DP := RelativeRoot.dynamicRootProductOfLargerSupport hS i i
    (fun _ h => h) ν nP aP haPi haP hdP
  let EN := RelativeRoot.dynamicRootProductOfLargerSupport hS i (i ≫ q)
    hsub (-ν) nN aN haNi haN hdN
  let EP := RelativeRoot.dynamicRootProductOfLargerSupport hS i (i ≫ q)
    hsub ν nP aP haPi haP hdP
  have hposN (r : Fin nN) : 0 < latticePairing S (aN r) (-ν) :=
    ((haN ▸ Set.mem_range_self r) : aN r ∈
      RelativeRoot.indivisiblePositiveRoots i (-ν)).2
  have hposP (r : Fin nP) : 0 < latticePairing S (aP r) ν :=
    ((haP ▸ Set.mem_range_self r) : aP r ∈
      RelativeRoot.indivisiblePositiveRoots i ν).2
  let : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom
  let χ := CommGroupScheme.groupHom ν ≫ (i ≫ q)
  let W := Dynamic.Affine.centralizerScheme χ
  let lZ : W ⟶ H := Dynamic.Affine.centralizerHom χ
  have hlZ : (torusCentralizer (i ≫ q)).IsRepresentedBy lZ := by
    rw [← hS.dynamicCentralizer_eq_torusCentralizer (i ≫ q) ν hνH]
    exact Dynamic.Affine.isRepresentedBy_centralizerHom χ
  let d := chartData DN.factorInclusions jZ DP.factorInclusions
  let e := chartData EN.factorInclusions lZ EP.factorInclusions
  let A := fun r => (d r).1
  let B := fun r => (e r).1
  let j : ∀ r, A r ⟶ G := fun r => (d r).2
  let l : ∀ r, B r ⟶ H := fun r => (e r).2
  have hjN (r : Fin nN) : (RelativeRoot.subgroup i (aN r)).IsRepresentedBy
      (j (Fin.castAdd (nP + 1) r)) := by
    dsimp only [j, A, d, chartData]
    rw [Fin.addCases_left]
    exact DN.factorRep r
  have hjP (r : Fin nP) : (RelativeRoot.subgroup i (aP r)).IsRepresentedBy
      (j (Fin.natAdd nN r.succ)) := by
    dsimp only [j, A, d, chartData]
    rw [Fin.addCases_right, Fin.cases_succ]
    exact DP.factorRep r
  have hjZ' : (torusCentralizer i).IsRepresentedBy (j (Fin.natAdd nN 0)) := by
    dsimp only [j, A, d, chartData]
    rw [Fin.addCases_right, Fin.cases_zero]
    exact hjZ
  have hlN (r : Fin nN) : (RelativeRoot.subgroup (i ≫ q) (aN r)).IsRepresentedBy
      (l (Fin.castAdd (nP + 1) r)) := by
    dsimp only [l, B, e, chartData]
    rw [Fin.addCases_left]
    exact EN.factorRep r
  have hlP (r : Fin nP) : (RelativeRoot.subgroup (i ≫ q) (aP r)).IsRepresentedBy
      (l (Fin.natAdd nN r.succ)) := by
    dsimp only [l, B, e, chartData]
    rw [Fin.addCases_right, Fin.cases_succ]
    exact EP.factorRep r
  have hlZ' : (torusCentralizer (i ≫ q)).IsRepresentedBy (l (Fin.natAdd nN 0)) := by
    dsimp only [l, B, e, chartData]
    rw [Fin.addCases_right, Fin.cases_zero]
    exact hlZ
  let fN (r : Fin nN) := RelativeRoot.SmoothQuotient.rootMap
    i q (aN r) (j (Fin.castAdd (nP + 1) r)) (l (Fin.castAdd (nP + 1) r))
      (hjN r) (hlN r)
  let fP (r : Fin nP) := RelativeRoot.SmoothQuotient.rootMap
    i q (aP r) (j (Fin.natAdd nN r.succ)) (l (Fin.natAdd nN r.succ))
      (hjP r) (hlP r)
  let fZ := TorusSmoothQuotient.centralizerMap i q
    (j (Fin.natAdd nN 0)) (l (Fin.natAdd nN 0)) hjZ' hlZ'
  let f : ∀ r, A r ⟶ B r := Fin.addCases fN (Fin.cases fZ fP)
  have hf (r) : j r ≫ q = f r ≫ l r := by
    induction r using Fin.addCases with
    | left r =>
      simpa only [f, Fin.addCases_left] using
        (RelativeRoot.SmoothQuotient.rootMap_comp i q (aN r)
          (j (Fin.castAdd (nP + 1) r)) (l (Fin.castAdd (nP + 1) r))
            (hjN r) (hlN r)).symm
    | right r =>
      induction r using Fin.cases with
      | zero =>
        simpa only [f, Fin.addCases_right, Fin.cases_zero] using
          (TorusSmoothQuotient.centralizerMap_comp i q
            (j (Fin.natAdd nN 0)) (l (Fin.natAdd nN 0)) hjZ' hlZ').symm
      | succ r =>
        simpa only [f, Fin.addCases_right, Fin.cases_succ] using
          (RelativeRoot.SmoothQuotient.rootMap_comp i q (aP r)
            (j (Fin.natAdd nN r.succ)) (l (Fin.natAdd nN r.succ))
              (hjP r) (hlP r)).symm
  let : IsOpenImmersion (RelativeRoot.orderedMultiplication j).left :=
    RootCentralizerOpenChart.isOpenImmersion_orderedMultiplication
      hS i ν hν aN aP DN DP hposN hposP j hjN hjZ' hjP
  let : IsOpenImmersion (RelativeRoot.orderedMultiplication l).left :=
    RootCentralizerOpenChart.isOpenImmersion_orderedMultiplication
      hS (i ≫ q) ν hνH aN aP EN EP hposN hposP l hlN hlZ' hlP
  let : Mono (RelativeRoot.orderedMultiplication l) := Over.mono_of_mono_left _
  let : LocallyOfFiniteType (kernel q).X.hom := by
    rw [← Over.w (kernelι q).hom.hom]
    infer_instance
  apply RelativeRoot.smooth_kernel_of_orderedOpenCharts j l q f hf
  intro r
  have hlmono : Mono (l r).hom.hom := by
    induction r using Fin.addCases with
    | left r => exact (hlN r).1
    | right r =>
      induction r using Fin.cases with
      | zero => exact hlZ'.1
      | succ r => exact (hlP r).1
  apply smooth_kernel_of_monic_comp (f r) (l r)
  rw [← hf r]
  induction r using Fin.addCases with
  | left r =>
    exact hroot (aN r) ((haN ▸ Set.mem_range_self r) : aN r ∈
      RelativeRoot.indivisiblePositiveRoots i (-ν)).1.1 _ _ (hjN r)
  | right r =>
    induction r using Fin.cases with
    | zero =>
        dsimp only [j, A, d, chartData]
        rw [Fin.addCases_right, Fin.cases_zero]
        exact hcenter
    | succ r =>
      exact hroot (aP r) ((haP ▸ Set.mem_range_self r) : aP r ∈
        RelativeRoot.indivisiblePositiveRoots i ν).1.1 _ _ (hjP r)

end Field

end Langlands.BruhatTits.IntegralModels.RootCentralizerKernel
