import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardThetaFixedFiniteness
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardThetaFixedStandardComparison

/-! # Support at a fixed level and the conditional VIII.1.3(ii) adapters -/

noncomputable section

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel

namespace Langlands.HarishChandraSchwartz

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom] {i : S.toGrp ⟶ G}

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace rationalInducedSecondCountable
  rationalInducedT2 rationalInducedNonarchimedean

open RationalSemistandard

section FixedSupport

variable {T : SemistandardSpectralIndex i → CommGroupScheme (Spec (CommRingCat.of F))}
  (a : ∀ p, (T p).toGrp ⟶ (chosenLeviModel p).scheme)
  (ha : ∀ p, IsSplitComponent (a p))
  [∀ p, ((chosenLeviModel p).splitCenter (a p)).Normal]
  [∀ p, MeasurableSpace (levi p ⧸ (chosenLeviModel p).splitCenter (a p))]
  (mu : ∀ p, Measure (levi p ⧸ (chosenLeviModel p).splitCenter (a p)))
  [∀ p, (mu p).IsHaarMeasure]

/-! ## Families supported in `Theta^H` -/

/-- Full families whose every nonzero component has its index in `Theta^H`. -/
def rationalSemistandardThetaFixedSupported (H : Subgroup (rationalPoints G)) :
    Submodule ℂ (RationalSemistandardThetaSections.{u, uV} a ha mu) where
  carrier := {f | rationalSemistandardThetaSupport.{u, uV} a ha mu f ⊆
    rationalSemistandardThetaFixed.{u, uV} a ha mu H}
  zero_mem' := by
    change rationalSemistandardThetaSupport.{u, uV} a ha mu 0 ⊆ _
    rw [rationalSemistandardThetaSupport_zero]
    exact Set.empty_subset _
  add_mem' {f g} hf hg :=
    (rationalSemistandardThetaSupport_add_subset.{u, uV} a ha mu f g).trans
      (Set.union_subset hf hg)
  smul_mem' c f hf :=
    (rationalSemistandardThetaSupport_smul_subset.{u, uV} a ha mu c f).trans hf

theorem mem_rationalSemistandardThetaFixedSupported (H : Subgroup (rationalPoints G))
    (f : RationalSemistandardThetaSections.{u, uV} a ha mu) :
    f ∈ rationalSemistandardThetaFixedSupported.{u, uV} a ha mu H ↔
      rationalSemistandardThetaSupport.{u, uV} a ha mu f ⊆
        rationalSemistandardThetaFixed.{u, uV} a ha mu H := Iff.rfl

/-- Componentwise form: every nonzero component has its index in `Theta^H`. -/
theorem mem_rationalSemistandardThetaFixedSupported_iff_forall
    (H : Subgroup (rationalPoints G)) (f : RationalSemistandardThetaSections.{u, uV} a ha mu) :
    f ∈ rationalSemistandardThetaFixedSupported.{u, uV} a ha mu H ↔
      ∀ t, f t ≠ 0 → t ∈ rationalSemistandardThetaFixed.{u, uV} a ha mu H := Iff.rfl

/-- A smaller level allows more indices. -/
theorem rationalSemistandardThetaFixedSupported_antitone :
    Antitone (rationalSemistandardThetaFixedSupported.{u, uV} a ha mu) :=
  fun _ _ hLH _ hf => hf.trans (rationalSemistandardThetaFixed_antitone.{u, uV} a ha mu hLH)

/-- Families whose nonzero components at proper indices (`P ≠ G`) all have their
index in `Theta^H`. Nothing is required at `P = G`. -/
def rationalSemistandardThetaProperFixedSupported (H : Subgroup (rationalPoints G)) :
    Submodule ℂ (RationalSemistandardThetaSections.{u, uV} a ha mu) where
  carrier := {f | rationalSemistandardThetaSupport.{u, uV} a ha mu f ∩
    rationalSemistandardThetaProper.{u, uV} a ha mu ⊆
      rationalSemistandardThetaFixed.{u, uV} a ha mu H}
  zero_mem' := by
    change rationalSemistandardThetaSupport.{u, uV} a ha mu 0 ∩ _ ⊆ _
    rw [rationalSemistandardThetaSupport_zero, Set.empty_inter]
    exact Set.empty_subset _
  add_mem' {f g} hf hg := by
    intro t ht
    rcases rationalSemistandardThetaSupport_add_subset.{u, uV} a ha mu f g ht.1 with h | h
    · exact hf ⟨h, ht.2⟩
    · exact hg ⟨h, ht.2⟩
  smul_mem' c f hf := fun t ht =>
    hf ⟨rationalSemistandardThetaSupport_smul_subset.{u, uV} a ha mu c f ht.1, ht.2⟩

theorem mem_rationalSemistandardThetaProperFixedSupported (H : Subgroup (rationalPoints G))
    (f : RationalSemistandardThetaSections.{u, uV} a ha mu) :
    f ∈ rationalSemistandardThetaProperFixedSupported.{u, uV} a ha mu H ↔
      rationalSemistandardThetaSupport.{u, uV} a ha mu f ∩
          rationalSemistandardThetaProper.{u, uV} a ha mu ⊆
        rationalSemistandardThetaFixed.{u, uV} a ha mu H := Iff.rfl

/-- The proper condition is exactly the full condition for the proper part. -/
theorem mem_rationalSemistandardThetaProperFixedSupported_iff_properPart
    (H : Subgroup (rationalPoints G)) (f : RationalSemistandardThetaSections.{u, uV} a ha mu) :
    f ∈ rationalSemistandardThetaProperFixedSupported.{u, uV} a ha mu H ↔
      rationalSemistandardThetaProperPart.{u, uV} a ha mu f ∈
        rationalSemistandardThetaFixedSupported.{u, uV} a ha mu H := by
  rw [mem_rationalSemistandardThetaProperFixedSupported, mem_rationalSemistandardThetaFixedSupported,
    rationalSemistandardThetaSupport_properPart]

theorem rationalSemistandardThetaFixedSupported_le_proper (H : Subgroup (rationalPoints G)) :
    rationalSemistandardThetaFixedSupported.{u, uV} a ha mu H ≤
      rationalSemistandardThetaProperFixedSupported.{u, uV} a ha mu H :=
  fun _ hf => Set.inter_subset_left.trans hf

theorem rationalSemistandardThetaProperFixedSupported_antitone :
    Antitone (rationalSemistandardThetaProperFixedSupported.{u, uV} a ha mu) :=
  fun _ _ hLH _ hf => hf.trans (rationalSemistandardThetaFixed_antitone.{u, uV} a ha mu hLH)

/-! ## The finite-index step of VIII.1.3(ii) -/

variable {a ha mu} in
/-- Full form of the deduction in VIII.1.3(ii): support inside `Theta^H` and
finiteness of `Theta^H` give finite support. -/
theorem finite_rationalSemistandardThetaSupport_of_fixedSupported
    {H : Subgroup (rationalPoints G)} {f : RationalSemistandardThetaSections.{u, uV} a ha mu}
    (hf : f ∈ rationalSemistandardThetaFixedSupported.{u, uV} a ha mu H)
    (hfin : (rationalSemistandardThetaFixed.{u, uV} a ha mu H).Finite) :
    (rationalSemistandardThetaSupport.{u, uV} a ha mu f).Finite :=
  hfin.subset hf

variable {a ha mu} in
/-- Proper form: only `Theta^H - Theta^H_G` must be finite, and only the proper
part of the support is concluded finite. -/
theorem finite_rationalSemistandardThetaSupport_inter_proper_of_properFixedSupported
    {H : Subgroup (rationalPoints G)} {f : RationalSemistandardThetaSections.{u, uV} a ha mu}
    (hf : f ∈ rationalSemistandardThetaProperFixedSupported.{u, uV} a ha mu H)
    (hfin : (rationalSemistandardThetaFixed.{u, uV} a ha mu H ∩
      rationalSemistandardThetaProper.{u, uV} a ha mu).Finite) :
    (rationalSemistandardThetaSupport.{u, uV} a ha mu f ∩
      rationalSemistandardThetaProper.{u, uV} a ha mu).Finite :=
  hfin.subset (Set.subset_inter hf Set.inter_subset_right)

/-! ## Smooth families supported at a fixed level -/

variable (d : ∀ p : SemistandardSpectralIndex i, CompactData p)

/-- Families with coherent smooth components at every index and support in
`Theta^H`. No finiteness is part of this submodule. -/
def rationalSemistandardThetaFixedSmooth (H : Subgroup (rationalPoints G)) :
    Submodule ℂ (RationalSemistandardThetaSections.{u, uV} a ha mu) where
  carrier := {f | (∀ t, f t ∈ rationalSemistandardThetaComponentSpace.{u, uV} a ha mu d t) ∧
    f ∈ rationalSemistandardThetaFixedSupported.{u, uV} a ha mu H}
  zero_mem' := ⟨fun _ => Submodule.zero_mem _, Submodule.zero_mem _⟩
  add_mem' hf hg :=
    ⟨fun t => Submodule.add_mem _ (hf.1 t) (hg.1 t), Submodule.add_mem _ hf.2 hg.2⟩
  smul_mem' c _ hf := ⟨fun t => Submodule.smul_mem _ c (hf.1 t), Submodule.smul_mem _ c hf.2⟩

theorem mem_rationalSemistandardThetaFixedSmooth (H : Subgroup (rationalPoints G))
    (f : RationalSemistandardThetaSections.{u, uV} a ha mu) :
    f ∈ rationalSemistandardThetaFixedSmooth.{u, uV} a ha mu d H ↔
      (∀ t, f t ∈ rationalSemistandardThetaComponentSpace.{u, uV} a ha mu d t) ∧
        f ∈ rationalSemistandardThetaFixedSupported.{u, uV} a ha mu H := Iff.rfl

/-- Families with coherent smooth components at proper indices and proper support
in `Theta^H`. Nothing is required at `P = G`. -/
def rationalSemistandardThetaProperFixedSmooth (H : Subgroup (rationalPoints G)) :
    Submodule ℂ (RationalSemistandardThetaSections.{u, uV} a ha mu) where
  carrier := {f | (∀ t ∈ rationalSemistandardThetaProper.{u, uV} a ha mu,
      f t ∈ rationalSemistandardThetaComponentSpace.{u, uV} a ha mu d t) ∧
    f ∈ rationalSemistandardThetaProperFixedSupported.{u, uV} a ha mu H}
  zero_mem' := ⟨fun _ _ => Submodule.zero_mem _, Submodule.zero_mem _⟩
  add_mem' hf hg :=
    ⟨fun t ht => Submodule.add_mem _ (hf.1 t ht) (hg.1 t ht), Submodule.add_mem _ hf.2 hg.2⟩
  smul_mem' c _ hf :=
    ⟨fun t ht => Submodule.smul_mem _ c (hf.1 t ht), Submodule.smul_mem _ c hf.2⟩

theorem mem_rationalSemistandardThetaProperFixedSmooth (H : Subgroup (rationalPoints G))
    (f : RationalSemistandardThetaSections.{u, uV} a ha mu) :
    f ∈ rationalSemistandardThetaProperFixedSmooth.{u, uV} a ha mu d H ↔
      (∀ t ∈ rationalSemistandardThetaProper.{u, uV} a ha mu,
        f t ∈ rationalSemistandardThetaComponentSpace.{u, uV} a ha mu d t) ∧
        f ∈ rationalSemistandardThetaProperFixedSupported.{u, uV} a ha mu H := Iff.rfl

theorem rationalSemistandardThetaFixedSmooth_le_proper (H : Subgroup (rationalPoints G)) :
    rationalSemistandardThetaFixedSmooth.{u, uV} a ha mu d H ≤
      rationalSemistandardThetaProperFixedSmooth.{u, uV} a ha mu d H :=
  fun _ hf => ⟨fun t _ => hf.1 t, rationalSemistandardThetaFixedSupported_le_proper a ha mu H hf.2⟩

theorem rationalSemistandardThetaFixedSmooth_antitone :
    Antitone (rationalSemistandardThetaFixedSmooth.{u, uV} a ha mu d) :=
  fun _ _ hLH _ hf => ⟨hf.1, rationalSemistandardThetaFixedSupported_antitone a ha mu hLH hf.2⟩

theorem rationalSemistandardThetaProperFixedSmooth_antitone :
    Antitone (rationalSemistandardThetaProperFixedSmooth.{u, uV} a ha mu d) :=
  fun _ _ hLH _ hf =>
    ⟨hf.1, rationalSemistandardThetaProperFixedSupported_antitone a ha mu hLH hf.2⟩

/-! ## Conditional maps into `C^infinity(Theta)` -/

variable {a ha mu} in
/-- Full VIII.1.3(ii) adapter: if `Theta^H` is finite, a family with smooth
components supported in `Theta^H` lies in the direct sum `C^infinity(Theta)`. -/
def rationalSemistandardThetaSmoothOfFixed {H : Subgroup (rationalPoints G)}
    (hfin : (rationalSemistandardThetaFixed.{u, uV} a ha mu H).Finite) :
    rationalSemistandardThetaFixedSmooth.{u, uV} a ha mu d H →ₗ[ℂ]
      rationalSemistandardThetaSmoothSections.{u, uV} a ha mu d where
  toFun f := rationalSemistandardThetaSmoothOfFinite.{u, uV} a ha mu d f.val f.property.1
    (finite_rationalSemistandardThetaSupport_of_fixedSupported f.property.2 hfin)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable {a ha mu} in
@[simp] theorem rationalSemistandardThetaSmoothOfFixed_val {H : Subgroup (rationalPoints G)}
    (hfin : (rationalSemistandardThetaFixed.{u, uV} a ha mu H).Finite)
    (f : rationalSemistandardThetaFixedSmooth.{u, uV} a ha mu d H) :
    (rationalSemistandardThetaSmoothOfFixed.{u, uV} d hfin f).val = f.val := rfl

variable {a ha mu} in
/-- The map does not depend on the level used to certify finite support. -/
theorem rationalSemistandardThetaSmoothOfFixed_of_le {L H : Subgroup (rationalPoints G)}
    (hLH : L ≤ H) (hfinL : (rationalSemistandardThetaFixed.{u, uV} a ha mu L).Finite)
    (hfinH : (rationalSemistandardThetaFixed.{u, uV} a ha mu H).Finite)
    (f : rationalSemistandardThetaFixedSmooth.{u, uV} a ha mu d H) :
    rationalSemistandardThetaSmoothOfFixed.{u, uV} d hfinL
        ⟨f.val, rationalSemistandardThetaFixedSmooth_antitone a ha mu d hLH f.property⟩ =
      rationalSemistandardThetaSmoothOfFixed.{u, uV} d hfinH f := rfl

variable {a ha mu} in
/-- Proper VIII.1.3(ii) adapter: finiteness of `Theta^H - Theta^H_G` alone puts
the proper part of a family with smooth proper components and proper support in
`Theta^H` into `C^infinity(Theta)`. Its value is the extension by zero across
`P = G`. -/
def rationalSemistandardThetaProperSmoothOfFixed {H : Subgroup (rationalPoints G)}
    (hfin : (rationalSemistandardThetaFixed.{u, uV} a ha mu H ∩
      rationalSemistandardThetaProper.{u, uV} a ha mu).Finite) :
    rationalSemistandardThetaProperFixedSmooth.{u, uV} a ha mu d H →ₗ[ℂ]
      rationalSemistandardThetaSmoothSections.{u, uV} a ha mu d where
  toFun f := rationalSemistandardThetaProperSmoothOfFinite.{u, uV} a ha mu d f.val f.property.1
    (finite_rationalSemistandardThetaSupport_inter_proper_of_properFixedSupported
      f.property.2 hfin)
  map_add' f g := Subtype.ext (map_add (rationalSemistandardThetaProperPart.{u, uV} a ha mu)
    f.val g.val)
  map_smul' c f := Subtype.ext (map_smul (rationalSemistandardThetaProperPart.{u, uV} a ha mu)
    c f.val)

variable {a ha mu} in
@[simp] theorem rationalSemistandardThetaProperSmoothOfFixed_val
    {H : Subgroup (rationalPoints G)}
    (hfin : (rationalSemistandardThetaFixed.{u, uV} a ha mu H ∩
      rationalSemistandardThetaProper.{u, uV} a ha mu).Finite)
    (f : rationalSemistandardThetaProperFixedSmooth.{u, uV} a ha mu d H) :
    (rationalSemistandardThetaProperSmoothOfFixed.{u, uV} d hfin f).val =
      rationalSemistandardThetaProperPart.{u, uV} a ha mu f.val := rfl

variable {a ha mu} in
/-- The proper-index form: a finitely supported family on `Theta - Theta_G`. -/
def rationalSemistandardProperSmoothOfFixed {H : Subgroup (rationalPoints G)}
    (hfin : (rationalSemistandardThetaFixed.{u, uV} a ha mu H ∩
      rationalSemistandardThetaProper.{u, uV} a ha mu).Finite) :
    rationalSemistandardThetaProperFixedSmooth.{u, uV} a ha mu d H →ₗ[ℂ]
      FiniteSupportSections.submodule
        (fun t : RationalSemistandardProperTheta.{u, uV} a ha mu =>
          rationalSemistandardThetaComponentSpace.{u, uV} a ha mu d t.val) where
  toFun f := rationalSemistandardProperSmoothOfFinite.{u, uV} a ha mu d f.val f.property.1
    (finite_rationalSemistandardThetaSupport_inter_proper_of_properFixedSupported
      f.property.2 hfin)
  map_add' f g := Subtype.ext (map_add (rationalSemistandardProperRestrict.{u, uV} a ha mu)
    f.val g.val)
  map_smul' c f := Subtype.ext (map_smul (rationalSemistandardProperRestrict.{u, uV} a ha mu)
    c f.val)

variable {a ha mu} in
@[simp] theorem rationalSemistandardProperSmoothOfFixed_val {H : Subgroup (rationalPoints G)}
    (hfin : (rationalSemistandardThetaFixed.{u, uV} a ha mu H ∩
      rationalSemistandardThetaProper.{u, uV} a ha mu).Finite)
    (f : rationalSemistandardThetaProperFixedSmooth.{u, uV} a ha mu d H) :
    (rationalSemistandardProperSmoothOfFixed.{u, uV} d hfin f).val =
      rationalSemistandardProperRestrict.{u, uV} a ha mu f.val := rfl

variable {a ha mu} in
/-- Restricting the proper-supported family to the proper index type gives the
proper-index family. -/
theorem rationalSemistandardProperSmoothRestrict_properSmoothOfFixed
    {H : Subgroup (rationalPoints G)}
    (hfin : (rationalSemistandardThetaFixed.{u, uV} a ha mu H ∩
      rationalSemistandardThetaProper.{u, uV} a ha mu).Finite)
    (f : rationalSemistandardThetaProperFixedSmooth.{u, uV} a ha mu d H) :
    rationalSemistandardProperSmoothRestrict.{u, uV} a ha mu d
        (rationalSemistandardThetaProperSmoothOfFixed.{u, uV} d hfin f) =
      rationalSemistandardProperSmoothOfFixed.{u, uV} d hfin f :=
  rationalSemistandardProperSmoothRestrict_properSmoothOfFinite a ha mu d f.val f.property.1
    (finite_rationalSemistandardThetaSupport_inter_proper_of_properFixedSupported
      f.property.2 hfin)

variable {a ha mu} in
/-- When the full fixed set is finite, the proper part of the full map is the
proper map; the proper map needs only the finiteness of the proper part. -/
theorem rationalSemistandardThetaSmoothProperPart_smoothOfFixed
    {H : Subgroup (rationalPoints G)}
    (hfin : (rationalSemistandardThetaFixed.{u, uV} a ha mu H).Finite)
    (f : rationalSemistandardThetaFixedSmooth.{u, uV} a ha mu d H) :
    rationalSemistandardThetaSmoothProperPart.{u, uV} a ha mu d
        (rationalSemistandardThetaSmoothOfFixed.{u, uV} d hfin f) =
      rationalSemistandardThetaProperSmoothOfFixed.{u, uV} d
        (hfin.subset Set.inter_subset_left)
        ⟨f.val, rationalSemistandardThetaFixedSmooth_le_proper a ha mu d H f.property⟩ := rfl

/-! ## Conditional VIII.1.3(ii) from the VIII.1.3(i) adapters -/

variable [∀ p, BorelSpace (levi p ⧸ (chosenLeviModel p).splitCenter (a p))]

variable {a ha mu} in
/-- Full VIII.1.3(ii) for a family supported in `Theta^H`, from the full
VIII.1.3(i) adapter: geometric index finiteness, the normal-level comparison and
local VIII.1.2 for every semistandard Levi remain explicit premises. -/
theorem finite_rationalSemistandardThetaSupport_of_fixedSupported_of_local
    (K : OpenSubgroup (rationalPoints G)) (hKc : IsCompact (K : Set (rationalPoints G)))
    (hgeo : Finite (SemistandardSpectralIndex i))
    (hcomp : RationalSemistandardNormalLevelFixedComparison.{u, uV} (i := i) K)
    (hlocal : AllLeviOrbitFiniteness.{u, uV} (i := i))
    {H : Subgroup (rationalPoints G)} (hHo : IsOpen (H : Set (rationalPoints G)))
    (hHc : IsCompact (H : Set (rationalPoints G)))
    {f : RationalSemistandardThetaSections.{u, uV} a ha mu}
    (hf : f ∈ rationalSemistandardThetaFixedSupported.{u, uV} a ha mu H) :
    (rationalSemistandardThetaSupport.{u, uV} a ha mu f).Finite :=
  finite_rationalSemistandardThetaSupport_of_fixedSupported hf
    (finite_rationalSemistandardThetaFixed a ha mu K hKc hgeo hcomp hlocal H hHo hHc)

variable {a ha mu} in
/-- Proper VIII.1.3(ii) for a family whose proper support lies in `Theta^H`,
from the proper VIII.1.3(i) adapter: only proper Levis need local VIII.1.2 and
only proper indices need the normal-level comparison. -/
theorem finite_rationalSemistandardThetaSupport_inter_proper_of_properFixedSupported_of_local
    (K : OpenSubgroup (rationalPoints G)) (hKc : IsCompact (K : Set (rationalPoints G)))
    (hgeo : Finite (SemistandardSpectralIndex i))
    (hcomp : RationalProperSemistandardNormalLevelFixedComparison.{u, uV} (i := i) K)
    (hlocal : ProperLeviOrbitFiniteness.{u, uV} (i := i))
    {H : Subgroup (rationalPoints G)} (hHo : IsOpen (H : Set (rationalPoints G)))
    (hHc : IsCompact (H : Set (rationalPoints G)))
    {f : RationalSemistandardThetaSections.{u, uV} a ha mu}
    (hf : f ∈ rationalSemistandardThetaProperFixedSupported.{u, uV} a ha mu H) :
    (rationalSemistandardThetaSupport.{u, uV} a ha mu f ∩
      rationalSemistandardThetaProper.{u, uV} a ha mu).Finite :=
  finite_rationalSemistandardThetaSupport_inter_proper_of_properFixedSupported hf
    (finite_rationalProperSemistandardThetaFixed a ha mu K hKc hgeo hcomp hlocal H hHo hHc)

end FixedSupport

/-! ## Standard slice -/

section StandardComparison

variable {T : SemistandardSpectralIndex i → CommGroupScheme (Spec (CommRingCat.of F))}
  (a : ∀ p, (T p).toGrp ⟶ (chosenLeviModel p).scheme)
  (ha : ∀ p, IsSplitComponent (a p))
  [∀ p, ((chosenLeviModel p).splitCenter (a p)).Normal]
  [∀ p, MeasurableSpace (levi p ⧸ (chosenLeviModel p).splitCenter (a p))]
  (mu : ∀ p, Measure (levi p ⧸ (chosenLeviModel p).splitCenter (a p)))
  [∀ p, (mu p).IsHaarMeasure]
  {nu : cocharacterLattice S} (hG : IsConnectedReductive G)
  (hi : IsMaximalSplitTorus i) (hnu : IsGenericCocharacter i nu)
  {B : Finset (RationalPointFamily.SimpleRoot i nu) → CommGroupScheme (Spec (CommRingCat.of F))}
  (b : ∀ I, (B I).toGrp ⟶ Standard.leviScheme i nu (RationalPointFamily.rootSet i nu I))
  (hb : ∀ I, IsSplitComponent (b I))
  [∀ I, (rationalLeviSplitCenter I (b I)).Normal]
  [∀ I, MeasurableSpace (standardLeviPoints i nu (RationalPointFamily.rootSet i nu I) ⧸
    rationalLeviSplitCenter I (b I))]
  (eta : ∀ I, Measure (standardLeviPoints i nu (RationalPointFamily.rootSet i nu I) ⧸
    rationalLeviSplitCenter I (b I)))
  [∀ I, (eta I).IsHaarMeasure]
  [∀ I, BorelSpace
    (levi (standardIndex hG hi hnu I) ⧸
      (chosenLeviModel (standardIndex hG hi hnu I)).splitCenter
        (a (standardIndex hG hi hnu I)))]
  [∀ I, BorelSpace
    (levi (standardIndex hG hi hnu I) ⧸ rationalLeviSplitCenter I (b I))]
  (hds : RationalSemistandardStandardDiscreteSeriesComparison.{u, uV}
    a ha mu hG hi hnu b hb eta)

/-- The restriction to the existing standard product of a family supported in
the full `Theta^H` is supported in the existing standard `Theta^H`, using the
discrete-series comparison `hds` for the two Borel quotients. -/
theorem rationalStandardFullRestrict_support_subset_rationalThetaFixed
    {H : Subgroup (rationalPoints G)} {f : RationalSemistandardThetaSections.{u, uV} a ha mu}
    (hf : f ∈ rationalSemistandardThetaFixedSupported.{u, uV} a ha mu H) :
    {t : RationalStandardTheta.{u, uV} b hb eta |
      rationalStandardFullRestrict.{u, uV} a ha mu hG hi hnu b hb eta hds f t.1 t.2 ≠ 0} ⊆
      rationalThetaFixed.{u, uV} hG hi hnu b hb eta H :=
  (rationalStandardFullRestrict_support.{u, uV} a ha mu hG hi hnu b hb eta hds f).trans_subset
    ((Set.preimage_mono hf).trans
      (rationalSemistandardThetaFixed_standard_preimage a ha mu hG hi hnu b hb eta hds H).le)

end StandardComparison

end Langlands.HarishChandraSchwartz
