import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardSpectralFamily

/-! # Group and proper parts of the full semistandard spectral index -/

noncomputable section

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel

namespace Langlands.GroupScheme.SemistandardSpectralIndex

variable {k : Type u} [Field k] {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} {i : T.toGrp ⟶ G}

/-- Waldspurger's condition `P ≠ G`: the actual all-test parabolic subgroup
functor of the index is not the subgroup functor of all points of `G`. -/
def IsProper (p : SemistandardSpectralIndex i) : Prop := p.parabolic ≠ ⊤

theorem isProper_iff (p : SemistandardSpectralIndex i) :
    p.IsProper ↔ p.parabolic ≠ ⊤ := Iff.rfl

theorem not_isProper_iff (p : SemistandardSpectralIndex i) :
    ¬ p.IsProper ↔ p.parabolic = ⊤ := not_not

end Langlands.GroupScheme.SemistandardSpectralIndex

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

section Parts

variable {T : SemistandardSpectralIndex i → CommGroupScheme (Spec (CommRingCat.of F))}
  (a : ∀ p, (T p).toGrp ⟶ (chosenLeviModel p).scheme)
  (ha : ∀ p, IsSplitComponent (a p))
  [∀ p, ((chosenLeviModel p).splitCenter (a p)).Normal]
  [∀ p, MeasurableSpace (levi p ⧸ (chosenLeviModel p).splitCenter (a p))]
  (mu : ∀ p, Measure (levi p ⧸ (chosenLeviModel p).splitCenter (a p)))
  [∀ p, (mu p).IsHaarMeasure]

/-- The group part `Theta_G`: full indices `(O,P)` with `P = G`. -/
def rationalSemistandardThetaGroup : Set (RationalSemistandardTheta.{u, uV} a ha mu) :=
  {t | t.1.parabolic = ⊤}

/-- The proper part `Theta - Theta_G`: full indices `(O,P)` with `P ≠ G`. -/
def rationalSemistandardThetaProper : Set (RationalSemistandardTheta.{u, uV} a ha mu) :=
  {t | t.1.IsProper}

@[simp] theorem mem_rationalSemistandardThetaGroup (t : RationalSemistandardTheta.{u, uV} a ha mu) :
    t ∈ rationalSemistandardThetaGroup.{u, uV} a ha mu ↔ t.1.parabolic = ⊤ := Iff.rfl

@[simp] theorem mem_rationalSemistandardThetaProper (t : RationalSemistandardTheta.{u, uV} a ha mu) :
    t ∈ rationalSemistandardThetaProper.{u, uV} a ha mu ↔ t.1.parabolic ≠ ⊤ := Iff.rfl

theorem compl_rationalSemistandardThetaGroup :
    (rationalSemistandardThetaGroup.{u, uV} a ha mu)ᶜ =
      rationalSemistandardThetaProper.{u, uV} a ha mu := rfl

theorem compl_rationalSemistandardThetaProper :
    (rationalSemistandardThetaProper.{u, uV} a ha mu)ᶜ =
      rationalSemistandardThetaGroup.{u, uV} a ha mu := by
  rw [← compl_rationalSemistandardThetaGroup, compl_compl]

theorem rationalSemistandardThetaGroup_union_proper :
    rationalSemistandardThetaGroup.{u, uV} a ha mu ∪
      rationalSemistandardThetaProper.{u, uV} a ha mu = Set.univ := by
  rw [← compl_rationalSemistandardThetaGroup, Set.union_compl_self]

theorem disjoint_rationalSemistandardThetaGroup_proper :
    Disjoint (rationalSemistandardThetaGroup.{u, uV} a ha mu)
      (rationalSemistandardThetaProper.{u, uV} a ha mu) := by
  rw [← compl_rationalSemistandardThetaGroup]
  exact disjoint_compl_right

/-- The index type of the proper part. -/
abbrev RationalSemistandardProperTheta : Type _ :=
  ↥(rationalSemistandardThetaProper.{u, uV} a ha mu)

/-! ## Restriction to the proper index type -/

/-- Restrict raw full families to the proper index type. -/
def rationalSemistandardProperRestrict :
    RationalSemistandardThetaSections.{u, uV} a ha mu →ₗ[ℂ]
      ∀ t : RationalSemistandardProperTheta.{u, uV} a ha mu,
        RationalSemistandardThetaSection.{u, uV} a ha mu t.val :=
  FiniteSupportSections.restrict Subtype.val

@[simp] theorem rationalSemistandardProperRestrict_apply
    (f : RationalSemistandardThetaSections.{u, uV} a ha mu)
    (t : RationalSemistandardProperTheta.{u, uV} a ha mu) :
    rationalSemistandardProperRestrict.{u, uV} a ha mu f t = f t.val := rfl

theorem rationalSemistandardProperRestrict_support
    (f : RationalSemistandardThetaSections.{u, uV} a ha mu) :
    FiniteSupportSections.support (rationalSemistandardProperRestrict.{u, uV} a ha mu f) =
      Subtype.val ⁻¹' rationalSemistandardThetaSupport.{u, uV} a ha mu f := rfl

/-- Finiteness of the proper restriction's support is exactly finiteness of the
proper part of the full support. -/
theorem finite_rationalSemistandardProperRestrict_support_iff
    (f : RationalSemistandardThetaSections.{u, uV} a ha mu) :
    (FiniteSupportSections.support (rationalSemistandardProperRestrict.{u, uV} a ha mu f)).Finite ↔
      (rationalSemistandardThetaSupport.{u, uV} a ha mu f ∩
        rationalSemistandardThetaProper.{u, uV} a ha mu).Finite := by
  rw [rationalSemistandardProperRestrict_support, Set.inter_comm]
  constructor
  · intro h
    have himg := h.image Subtype.val
    refine himg.subset ?_
    intro t ht
    exact ⟨⟨t, ht.1⟩, ht.2, rfl⟩
  · intro h
    refine (h.preimage Subtype.val_injective.injOn).subset ?_
    intro t ht
    exact ⟨t.property, ht⟩

variable (d : ∀ p : SemistandardSpectralIndex i, CompactData p)

/-- Restrict finitely supported smooth full families to the proper index type. -/
def rationalSemistandardProperSmoothRestrict :
    rationalSemistandardThetaSmoothSections.{u, uV} a ha mu d →ₗ[ℂ]
      FiniteSupportSections.submodule (fun t : RationalSemistandardProperTheta.{u, uV} a ha mu =>
        rationalSemistandardThetaComponentSpace.{u, uV} a ha mu d t.val) :=
  FiniteSupportSections.restrictSubmodule Subtype.val _ Subtype.val_injective

@[simp] theorem rationalSemistandardProperSmoothRestrict_val
    (f : rationalSemistandardThetaSmoothSections.{u, uV} a ha mu d)
    (t : RationalSemistandardProperTheta.{u, uV} a ha mu) :
    (rationalSemistandardProperSmoothRestrict.{u, uV} a ha mu d f).val t = f.val t.val := rfl

/-! ## Extension by zero across the group part -/

open Classical in
/-- Keep the components at `P ≠ G` and replace those at `P = G` by zero.
This is the shape of Waldspurger VIII.2's `psi`; it needs no support hypothesis. -/
def rationalSemistandardThetaProperPart :
    RationalSemistandardThetaSections.{u, uV} a ha mu →ₗ[ℂ]
      RationalSemistandardThetaSections.{u, uV} a ha mu where
  toFun f t := if t ∈ rationalSemistandardThetaProper.{u, uV} a ha mu then f t else 0
  map_add' f g := by
    funext t
    simp only [Pi.add_apply]
    split_ifs <;> simp
  map_smul' c f := by
    funext t
    simp only [Pi.smul_apply, RingHom.id_apply]
    split_ifs <;> simp

open Classical in
/-- Keep the components at `P = G` and replace those at `P ≠ G` by zero. -/
def rationalSemistandardThetaGroupPart :
    RationalSemistandardThetaSections.{u, uV} a ha mu →ₗ[ℂ]
      RationalSemistandardThetaSections.{u, uV} a ha mu where
  toFun f t := if t ∈ rationalSemistandardThetaGroup.{u, uV} a ha mu then f t else 0
  map_add' f g := by
    funext t
    simp only [Pi.add_apply]
    split_ifs <;> simp
  map_smul' c f := by
    funext t
    simp only [Pi.smul_apply, RingHom.id_apply]
    split_ifs <;> simp

variable {a ha mu} in
theorem rationalSemistandardThetaProperPart_apply_of_mem
    {t : RationalSemistandardTheta.{u, uV} a ha mu}
    (ht : t ∈ rationalSemistandardThetaProper.{u, uV} a ha mu)
    (f : RationalSemistandardThetaSections.{u, uV} a ha mu) :
    rationalSemistandardThetaProperPart.{u, uV} a ha mu f t = f t := by
  classical
  exact ite_eq_left ht

variable {a ha mu} in
theorem rationalSemistandardThetaProperPart_apply_of_not_mem
    {t : RationalSemistandardTheta.{u, uV} a ha mu}
    (ht : t ∉ rationalSemistandardThetaProper.{u, uV} a ha mu)
    (f : RationalSemistandardThetaSections.{u, uV} a ha mu) :
    rationalSemistandardThetaProperPart.{u, uV} a ha mu f t = 0 := by
  classical
  exact ite_eq_right ht

variable {a ha mu} in
theorem rationalSemistandardThetaProperPart_apply_of_mem_group
    {t : RationalSemistandardTheta.{u, uV} a ha mu}
    (ht : t ∈ rationalSemistandardThetaGroup.{u, uV} a ha mu)
    (f : RationalSemistandardThetaSections.{u, uV} a ha mu) :
    rationalSemistandardThetaProperPart.{u, uV} a ha mu f t = 0 :=
  rationalSemistandardThetaProperPart_apply_of_not_mem (fun hp => hp ht) f

variable {a ha mu} in
theorem rationalSemistandardThetaGroupPart_apply_of_mem
    {t : RationalSemistandardTheta.{u, uV} a ha mu}
    (ht : t ∈ rationalSemistandardThetaGroup.{u, uV} a ha mu)
    (f : RationalSemistandardThetaSections.{u, uV} a ha mu) :
    rationalSemistandardThetaGroupPart.{u, uV} a ha mu f t = f t := by
  classical
  exact ite_eq_left ht

variable {a ha mu} in
theorem rationalSemistandardThetaGroupPart_apply_of_not_mem
    {t : RationalSemistandardTheta.{u, uV} a ha mu}
    (ht : t ∉ rationalSemistandardThetaGroup.{u, uV} a ha mu)
    (f : RationalSemistandardThetaSections.{u, uV} a ha mu) :
    rationalSemistandardThetaGroupPart.{u, uV} a ha mu f t = 0 := by
  classical
  exact ite_eq_right ht

/-- Every full family is the sum of its proper and group parts. -/
theorem rationalSemistandardThetaProperPart_add_groupPart
    (f : RationalSemistandardThetaSections.{u, uV} a ha mu) :
    rationalSemistandardThetaProperPart.{u, uV} a ha mu f +
      rationalSemistandardThetaGroupPart.{u, uV} a ha mu f = f := by
  funext t
  rw [Pi.add_apply]
  by_cases hg : t ∈ rationalSemistandardThetaGroup.{u, uV} a ha mu
  · rw [rationalSemistandardThetaProperPart_apply_of_mem_group hg,
      rationalSemistandardThetaGroupPart_apply_of_mem hg, zero_add]
  · have hp : t ∈ rationalSemistandardThetaProper.{u, uV} a ha mu := hg
    rw [rationalSemistandardThetaProperPart_apply_of_mem hp,
      rationalSemistandardThetaGroupPart_apply_of_not_mem hg, add_zero]

/-- The support of the proper part is the proper part of the support. -/
theorem rationalSemistandardThetaSupport_properPart
    (f : RationalSemistandardThetaSections.{u, uV} a ha mu) :
    rationalSemistandardThetaSupport.{u, uV} a ha mu
        (rationalSemistandardThetaProperPart.{u, uV} a ha mu f) =
      rationalSemistandardThetaSupport.{u, uV} a ha mu f ∩
        rationalSemistandardThetaProper.{u, uV} a ha mu := by
  ext t
  rw [mem_rationalSemistandardThetaSupport, Set.mem_inter_iff,
    mem_rationalSemistandardThetaSupport]
  by_cases hp : t ∈ rationalSemistandardThetaProper.{u, uV} a ha mu
  · rw [rationalSemistandardThetaProperPart_apply_of_mem hp]
    exact ⟨fun hf => ⟨hf, hp⟩, fun hf => hf.1⟩
  · rw [rationalSemistandardThetaProperPart_apply_of_not_mem hp]
    exact ⟨fun h0 => (h0 rfl).elim, fun hf => (hp hf.2).elim⟩

/-- The support of the group part is the group part of the support. -/
theorem rationalSemistandardThetaSupport_groupPart
    (f : RationalSemistandardThetaSections.{u, uV} a ha mu) :
    rationalSemistandardThetaSupport.{u, uV} a ha mu
        (rationalSemistandardThetaGroupPart.{u, uV} a ha mu f) =
      rationalSemistandardThetaSupport.{u, uV} a ha mu f ∩
        rationalSemistandardThetaGroup.{u, uV} a ha mu := by
  ext t
  rw [mem_rationalSemistandardThetaSupport, Set.mem_inter_iff,
    mem_rationalSemistandardThetaSupport]
  by_cases hg : t ∈ rationalSemistandardThetaGroup.{u, uV} a ha mu
  · rw [rationalSemistandardThetaGroupPart_apply_of_mem hg]
    exact ⟨fun hf => ⟨hf, hg⟩, fun hf => hf.1⟩
  · rw [rationalSemistandardThetaGroupPart_apply_of_not_mem hg]
    exact ⟨fun h0 => (h0 rfl).elim, fun hf => (hg hf.2).elim⟩

/-- A family equals its proper part exactly when it is supported on `P ≠ G`. -/
theorem rationalSemistandardThetaProperPart_eq_self_iff
    (f : RationalSemistandardThetaSections.{u, uV} a ha mu) :
    rationalSemistandardThetaProperPart.{u, uV} a ha mu f = f ↔
      rationalSemistandardThetaSupport.{u, uV} a ha mu f ⊆
        rationalSemistandardThetaProper.{u, uV} a ha mu := by
  constructor
  · intro h
    rw [← h, rationalSemistandardThetaSupport_properPart]
    exact Set.inter_subset_right
  · intro h
    funext t
    by_cases hp : t ∈ rationalSemistandardThetaProper.{u, uV} a ha mu
    · exact rationalSemistandardThetaProperPart_apply_of_mem hp f
    · rw [rationalSemistandardThetaProperPart_apply_of_not_mem hp]
      by_contra hne
      exact hp (h (fun h0 => hne h0.symm))

theorem rationalSemistandardThetaProperPart_idem
    (f : RationalSemistandardThetaSections.{u, uV} a ha mu) :
    rationalSemistandardThetaProperPart.{u, uV} a ha mu
        (rationalSemistandardThetaProperPart.{u, uV} a ha mu f) =
      rationalSemistandardThetaProperPart.{u, uV} a ha mu f := by
  rw [rationalSemistandardThetaProperPart_eq_self_iff, rationalSemistandardThetaSupport_properPart]
  exact Set.inter_subset_right

/-- Restriction to the proper index type does not see the group part. -/
theorem rationalSemistandardProperRestrict_properPart
    (f : RationalSemistandardThetaSections.{u, uV} a ha mu) :
    rationalSemistandardProperRestrict.{u, uV} a ha mu
        (rationalSemistandardThetaProperPart.{u, uV} a ha mu f) =
      rationalSemistandardProperRestrict.{u, uV} a ha mu f :=
  funext fun t => rationalSemistandardThetaProperPart_apply_of_mem t.property f

/-- The proper part keeps every proper component in its coherent smooth space. -/
theorem rationalSemistandardThetaProperPart_mem_componentSpace
    (f : RationalSemistandardThetaSections.{u, uV} a ha mu)
    (hf : ∀ t ∈ rationalSemistandardThetaProper.{u, uV} a ha mu,
      f t ∈ rationalSemistandardThetaComponentSpace.{u, uV} a ha mu d t)
    (t : RationalSemistandardTheta.{u, uV} a ha mu) :
    rationalSemistandardThetaProperPart.{u, uV} a ha mu f t ∈
      rationalSemistandardThetaComponentSpace.{u, uV} a ha mu d t := by
  by_cases hp : t ∈ rationalSemistandardThetaProper.{u, uV} a ha mu
  · rw [rationalSemistandardThetaProperPart_apply_of_mem hp]
    exact hf t hp
  · rw [rationalSemistandardThetaProperPart_apply_of_not_mem hp]
    exact Submodule.zero_mem _

/-- The proper part as an endomorphism of `C^infinity(Theta)`. -/
def rationalSemistandardThetaSmoothProperPart :
    rationalSemistandardThetaSmoothSections.{u, uV} a ha mu d →ₗ[ℂ]
      rationalSemistandardThetaSmoothSections.{u, uV} a ha mu d where
  toFun f := ⟨rationalSemistandardThetaProperPart.{u, uV} a ha mu f.val,
    rationalSemistandardThetaProperPart_mem_componentSpace.{u, uV} a ha mu d f.val
      (fun t _ => f.property.1 t),
    f.property.2.subset
      ((rationalSemistandardThetaSupport_properPart.{u, uV} a ha mu f.val).trans_subset
        Set.inter_subset_left)⟩
  map_add' f g := Subtype.ext (map_add _ f.val g.val)
  map_smul' c f := Subtype.ext (map_smul _ c f.val)

@[simp] theorem rationalSemistandardThetaSmoothProperPart_val
    (f : rationalSemistandardThetaSmoothSections.{u, uV} a ha mu d) :
    (rationalSemistandardThetaSmoothProperPart.{u, uV} a ha mu d f).val =
      rationalSemistandardThetaProperPart.{u, uV} a ha mu f.val := rfl

/-! ## Conditional finite-support constructors -/

/-- A raw full family enters Waldspurger's direct sum `C^infinity(Theta)` only
through proofs of componentwise coherent smoothness and of finite support. -/
def rationalSemistandardThetaSmoothOfFinite
    (f : RationalSemistandardThetaSections.{u, uV} a ha mu)
    (hf : ∀ t, f t ∈ rationalSemistandardThetaComponentSpace.{u, uV} a ha mu d t)
    (hs : (rationalSemistandardThetaSupport.{u, uV} a ha mu f).Finite) :
    rationalSemistandardThetaSmoothSections.{u, uV} a ha mu d :=
  ⟨f, hf, hs⟩

@[simp] theorem rationalSemistandardThetaSmoothOfFinite_val
    (f : RationalSemistandardThetaSections.{u, uV} a ha mu)
    (hf : ∀ t, f t ∈ rationalSemistandardThetaComponentSpace.{u, uV} a ha mu d t)
    (hs : (rationalSemistandardThetaSupport.{u, uV} a ha mu f).Finite) :
    (rationalSemistandardThetaSmoothOfFinite.{u, uV} a ha mu d f hf hs).val = f := rfl

theorem rationalSemistandardThetaSmoothOfFinite_add
    (f g : RationalSemistandardThetaSections.{u, uV} a ha mu)
    (hf : ∀ t, f t ∈ rationalSemistandardThetaComponentSpace.{u, uV} a ha mu d t)
    (hg : ∀ t, g t ∈ rationalSemistandardThetaComponentSpace.{u, uV} a ha mu d t)
    (hfs : (rationalSemistandardThetaSupport.{u, uV} a ha mu f).Finite)
    (hgs : (rationalSemistandardThetaSupport.{u, uV} a ha mu g).Finite)
    (hfg : ∀ t, (f + g) t ∈ rationalSemistandardThetaComponentSpace.{u, uV} a ha mu d t)
    (hfgs : (rationalSemistandardThetaSupport.{u, uV} a ha mu (f + g)).Finite) :
    rationalSemistandardThetaSmoothOfFinite.{u, uV} a ha mu d (f + g) hfg hfgs =
      rationalSemistandardThetaSmoothOfFinite.{u, uV} a ha mu d f hf hfs +
        rationalSemistandardThetaSmoothOfFinite.{u, uV} a ha mu d g hg hgs := rfl

theorem rationalSemistandardThetaSmoothOfFinite_smul (c : ℂ)
    (f : RationalSemistandardThetaSections.{u, uV} a ha mu)
    (hf : ∀ t, f t ∈ rationalSemistandardThetaComponentSpace.{u, uV} a ha mu d t)
    (hfs : (rationalSemistandardThetaSupport.{u, uV} a ha mu f).Finite)
    (hcf : ∀ t, (c • f) t ∈ rationalSemistandardThetaComponentSpace.{u, uV} a ha mu d t)
    (hcfs : (rationalSemistandardThetaSupport.{u, uV} a ha mu (c • f)).Finite) :
    rationalSemistandardThetaSmoothOfFinite.{u, uV} a ha mu d (c • f) hcf hcfs =
      c • rationalSemistandardThetaSmoothOfFinite.{u, uV} a ha mu d f hf hfs := rfl

/-- The proper-supported family enters `C^infinity(Theta)` from smoothness and
finite support on `P ≠ G` alone; nothing is required at `P = G`. -/
def rationalSemistandardThetaProperSmoothOfFinite
    (f : RationalSemistandardThetaSections.{u, uV} a ha mu)
    (hf : ∀ t ∈ rationalSemistandardThetaProper.{u, uV} a ha mu,
      f t ∈ rationalSemistandardThetaComponentSpace.{u, uV} a ha mu d t)
    (hs : (rationalSemistandardThetaSupport.{u, uV} a ha mu f ∩
      rationalSemistandardThetaProper.{u, uV} a ha mu).Finite) :
    rationalSemistandardThetaSmoothSections.{u, uV} a ha mu d :=
  ⟨rationalSemistandardThetaProperPart.{u, uV} a ha mu f,
    rationalSemistandardThetaProperPart_mem_componentSpace.{u, uV} a ha mu d f hf,
    hs.subset (rationalSemistandardThetaSupport_properPart.{u, uV} a ha mu f).le⟩

@[simp] theorem rationalSemistandardThetaProperSmoothOfFinite_val
    (f : RationalSemistandardThetaSections.{u, uV} a ha mu)
    (hf : ∀ t ∈ rationalSemistandardThetaProper.{u, uV} a ha mu,
      f t ∈ rationalSemistandardThetaComponentSpace.{u, uV} a ha mu d t)
    (hs : (rationalSemistandardThetaSupport.{u, uV} a ha mu f ∩
      rationalSemistandardThetaProper.{u, uV} a ha mu).Finite) :
    (rationalSemistandardThetaProperSmoothOfFinite.{u, uV} a ha mu d f hf hs).val =
      rationalSemistandardThetaProperPart.{u, uV} a ha mu f := rfl

theorem rationalSemistandardThetaProperSmoothOfFinite_add
    (f g : RationalSemistandardThetaSections.{u, uV} a ha mu)
    (hf : ∀ t ∈ rationalSemistandardThetaProper.{u, uV} a ha mu,
      f t ∈ rationalSemistandardThetaComponentSpace.{u, uV} a ha mu d t)
    (hg : ∀ t ∈ rationalSemistandardThetaProper.{u, uV} a ha mu,
      g t ∈ rationalSemistandardThetaComponentSpace.{u, uV} a ha mu d t)
    (hfs : (rationalSemistandardThetaSupport.{u, uV} a ha mu f ∩
      rationalSemistandardThetaProper.{u, uV} a ha mu).Finite)
    (hgs : (rationalSemistandardThetaSupport.{u, uV} a ha mu g ∩
      rationalSemistandardThetaProper.{u, uV} a ha mu).Finite)
    (hfg : ∀ t ∈ rationalSemistandardThetaProper.{u, uV} a ha mu,
      (f + g) t ∈ rationalSemistandardThetaComponentSpace.{u, uV} a ha mu d t)
    (hfgs : (rationalSemistandardThetaSupport.{u, uV} a ha mu (f + g) ∩
      rationalSemistandardThetaProper.{u, uV} a ha mu).Finite) :
    rationalSemistandardThetaProperSmoothOfFinite.{u, uV} a ha mu d (f + g) hfg hfgs =
      rationalSemistandardThetaProperSmoothOfFinite.{u, uV} a ha mu d f hf hfs +
        rationalSemistandardThetaProperSmoothOfFinite.{u, uV} a ha mu d g hg hgs :=
  Subtype.ext (map_add _ f g)

theorem rationalSemistandardThetaProperSmoothOfFinite_smul (c : ℂ)
    (f : RationalSemistandardThetaSections.{u, uV} a ha mu)
    (hf : ∀ t ∈ rationalSemistandardThetaProper.{u, uV} a ha mu,
      f t ∈ rationalSemistandardThetaComponentSpace.{u, uV} a ha mu d t)
    (hfs : (rationalSemistandardThetaSupport.{u, uV} a ha mu f ∩
      rationalSemistandardThetaProper.{u, uV} a ha mu).Finite)
    (hcf : ∀ t ∈ rationalSemistandardThetaProper.{u, uV} a ha mu,
      (c • f) t ∈ rationalSemistandardThetaComponentSpace.{u, uV} a ha mu d t)
    (hcfs : (rationalSemistandardThetaSupport.{u, uV} a ha mu (c • f) ∩
      rationalSemistandardThetaProper.{u, uV} a ha mu).Finite) :
    rationalSemistandardThetaProperSmoothOfFinite.{u, uV} a ha mu d (c • f) hcf hcfs =
      c • rationalSemistandardThetaProperSmoothOfFinite.{u, uV} a ha mu d f hf hfs :=
  Subtype.ext (map_smul _ c f)

/-- A fully finite smooth family has the same proper-supported family. -/
theorem rationalSemistandardThetaSmoothProperPart_smoothOfFinite
    (f : RationalSemistandardThetaSections.{u, uV} a ha mu)
    (hf : ∀ t, f t ∈ rationalSemistandardThetaComponentSpace.{u, uV} a ha mu d t)
    (hs : (rationalSemistandardThetaSupport.{u, uV} a ha mu f).Finite) :
    rationalSemistandardThetaSmoothProperPart.{u, uV} a ha mu d
        (rationalSemistandardThetaSmoothOfFinite.{u, uV} a ha mu d f hf hs) =
      rationalSemistandardThetaProperSmoothOfFinite.{u, uV} a ha mu d f
        (fun t _ => hf t) (hs.subset Set.inter_subset_left) := rfl

/-- The proper restriction as a finitely supported family on the proper index
type, from smoothness and finite support on `P ≠ G` alone. -/
def rationalSemistandardProperSmoothOfFinite
    (f : RationalSemistandardThetaSections.{u, uV} a ha mu)
    (hf : ∀ t ∈ rationalSemistandardThetaProper.{u, uV} a ha mu,
      f t ∈ rationalSemistandardThetaComponentSpace.{u, uV} a ha mu d t)
    (hs : (rationalSemistandardThetaSupport.{u, uV} a ha mu f ∩
      rationalSemistandardThetaProper.{u, uV} a ha mu).Finite) :
    FiniteSupportSections.submodule (fun t : RationalSemistandardProperTheta.{u, uV} a ha mu =>
      rationalSemistandardThetaComponentSpace.{u, uV} a ha mu d t.val) :=
  ⟨rationalSemistandardProperRestrict.{u, uV} a ha mu f, fun t => hf t.val t.property,
    (finite_rationalSemistandardProperRestrict_support_iff.{u, uV} a ha mu f).2 hs⟩

@[simp] theorem rationalSemistandardProperSmoothOfFinite_val
    (f : RationalSemistandardThetaSections.{u, uV} a ha mu)
    (hf : ∀ t ∈ rationalSemistandardThetaProper.{u, uV} a ha mu,
      f t ∈ rationalSemistandardThetaComponentSpace.{u, uV} a ha mu d t)
    (hs : (rationalSemistandardThetaSupport.{u, uV} a ha mu f ∩
      rationalSemistandardThetaProper.{u, uV} a ha mu).Finite) :
    (rationalSemistandardProperSmoothOfFinite.{u, uV} a ha mu d f hf hs).val =
      rationalSemistandardProperRestrict.{u, uV} a ha mu f := rfl

/-- The two proper constructions agree: restricting the proper-supported family
to the proper index type gives the proper-index family. -/
theorem rationalSemistandardProperSmoothRestrict_properSmoothOfFinite
    (f : RationalSemistandardThetaSections.{u, uV} a ha mu)
    (hf : ∀ t ∈ rationalSemistandardThetaProper.{u, uV} a ha mu,
      f t ∈ rationalSemistandardThetaComponentSpace.{u, uV} a ha mu d t)
    (hs : (rationalSemistandardThetaSupport.{u, uV} a ha mu f ∩
      rationalSemistandardThetaProper.{u, uV} a ha mu).Finite) :
    rationalSemistandardProperSmoothRestrict.{u, uV} a ha mu d
        (rationalSemistandardThetaProperSmoothOfFinite.{u, uV} a ha mu d f hf hs) =
      rationalSemistandardProperSmoothOfFinite.{u, uV} a ha mu d f hf hs :=
  Subtype.ext (rationalSemistandardProperRestrict_properPart.{u, uV} a ha mu f)

/-! ## The standard slice -/

section StandardRestriction

variable {nu : cocharacterLattice S} (hG : IsConnectedReductive G)
  (hi : IsMaximalSplitTorus i) (hnu : IsGenericCocharacter i nu)

theorem rationalSemistandardStandardIndex_mem_proper_iff
    (t : RationalSemistandardStandardTheta.{u, uV} a ha mu hG hi hnu) :
    rationalSemistandardStandardIndex.{u, uV} a ha mu hG hi hnu t ∈
        rationalSemistandardThetaProper.{u, uV} a ha mu ↔
      standardParabolic i nu (RationalPointFamily.rootSet i nu t.1) ≠ ⊤ := Iff.rfl

/-- The standard slice of the proper part keeps the proper standard components. -/
theorem rationalSemistandardStandardRestrict_properPart_of_mem
    (f : RationalSemistandardThetaSections.{u, uV} a ha mu)
    {t : RationalSemistandardStandardTheta.{u, uV} a ha mu hG hi hnu}
    (ht : rationalSemistandardStandardIndex.{u, uV} a ha mu hG hi hnu t ∈
      rationalSemistandardThetaProper.{u, uV} a ha mu) :
    rationalSemistandardStandardRestrict.{u, uV} a ha mu hG hi hnu
        (rationalSemistandardThetaProperPart.{u, uV} a ha mu f) t =
      rationalSemistandardStandardRestrict.{u, uV} a ha mu hG hi hnu f t :=
  rationalSemistandardThetaProperPart_apply_of_mem ht f

/-- The standard slice of the proper part vanishes at the standard group index. -/
theorem rationalSemistandardStandardRestrict_properPart_of_not_mem
    (f : RationalSemistandardThetaSections.{u, uV} a ha mu)
    {t : RationalSemistandardStandardTheta.{u, uV} a ha mu hG hi hnu}
    (ht : rationalSemistandardStandardIndex.{u, uV} a ha mu hG hi hnu t ∉
      rationalSemistandardThetaProper.{u, uV} a ha mu) :
    rationalSemistandardStandardRestrict.{u, uV} a ha mu hG hi hnu
        (rationalSemistandardThetaProperPart.{u, uV} a ha mu f) t = 0 :=
  rationalSemistandardThetaProperPart_apply_of_not_mem ht f

theorem rationalSemistandardStandardRestrict_properPart_support
    (f : RationalSemistandardThetaSections.{u, uV} a ha mu) :
    FiniteSupportSections.support
        (rationalSemistandardStandardRestrict.{u, uV} a ha mu hG hi hnu
          (rationalSemistandardThetaProperPart.{u, uV} a ha mu f)) =
      (rationalSemistandardStandardIndex.{u, uV} a ha mu hG hi hnu) ⁻¹'
        (rationalSemistandardThetaSupport.{u, uV} a ha mu f ∩
          rationalSemistandardThetaProper.{u, uV} a ha mu) := by
  rw [rationalSemistandardStandardRestrict_support, rationalSemistandardThetaSupport_properPart]

/-- The standard smooth slice of the smooth proper part. -/
theorem rationalSemistandardStandardSmoothRestrict_smoothProperPart_val
    (f : rationalSemistandardThetaSmoothSections.{u, uV} a ha mu d)
    (t : RationalSemistandardStandardTheta.{u, uV} a ha mu hG hi hnu) :
    (rationalSemistandardStandardSmoothRestrict.{u, uV} a ha mu d hG hi hnu
        (rationalSemistandardThetaSmoothProperPart.{u, uV} a ha mu d f)).val t =
      rationalSemistandardThetaProperPart.{u, uV} a ha mu f.val
        (rationalSemistandardStandardIndex.{u, uV} a ha mu hG hi hnu t) := rfl

end StandardRestriction

end Parts

end Langlands.HarishChandraSchwartz
