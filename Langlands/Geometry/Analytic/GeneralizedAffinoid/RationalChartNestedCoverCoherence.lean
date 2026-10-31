import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalChartNestedCoverFamily

/-! # Identity and composition of actual nested finite-cover transport -/

noncomputable section

universe u v

namespace Langlands.Analytic.PresentedAffinoidAlgebra

open CategoryTheory

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : PresentedAffinoidAlgebra K}

namespace Domain.FiniteCover

variable {U V : Domain K A} {Y : Type v} [TopologicalSpace Y]

/-- Restore a cover target through an actual domain isomorphism, retaining
every component algebra and its representation. -/
def changeTarget (a : U ≅ V) (c : FiniteCover U) : FiniteCover V where
  size := c.size
  obj := c.obj
  map i := c.map i ≫ a.hom
  covers x hx := c.covers x (a.inv.subset hx)

/-- Target restoration leaves all chosen refinement data unchanged. -/
def changeTargetRefinement (a : U ≅ V) {b c : FiniteCover U}
    (r : Refinement b c) : Refinement (changeTarget a b) (changeTarget a c) where
  index := r.index
  map := r.map

def changeTargetFunctor (a : U ≅ V) : FiniteCover U ⥤ FiniteCover V where
  obj c := changeTarget a c
  map r := changeTargetRefinement a r
  map_id _ := Refinement.ext rfl
  map_comp _ _ := Refinement.ext rfl

@[simp] theorem changeTarget_size (a : U ≅ V) (c : FiniteCover U) :
    (changeTarget a c).size = c.size := rfl

@[simp] theorem changeTarget_obj (a : U ≅ V) (c : FiniteCover U)
    (i : Fin c.size) : (changeTarget a c).obj i = c.obj i := rfl

@[simp] theorem changeTarget_map (a : U ≅ V) (c : FiniteCover U)
    (i : Fin c.size) : (changeTarget a c).map i = c.map i ≫ a.hom := rfl

@[simp] theorem changeTargetRefinement_index (a : U ≅ V)
    {b c : FiniteCover U} (r : Refinement b c) :
    (changeTargetRefinement a r).index = r.index := rfl

@[simp] theorem changeTargetRefinement_spectrumMap (a : U ≅ V)
    {b c : FiniteCover U} (r : Refinement b c) :
    (changeTargetRefinement a r).spectrumMap = r.spectrumMap := rfl

theorem changeTarget_componentMap (a : U ≅ V) (c : FiniteCover U)
    (i : Fin c.size) :
    (changeTarget a c).componentMap i = a.hom.locusMap.comp (c.componentMap i) := rfl

theorem changeTarget_totalMap (a : U ≅ V) (c : FiniteCover U) :
    (changeTarget a c).totalMap = a.hom.locusMap.comp c.totalMap := rfl

/-- Compatibility depends on the component loci, which target restoration
does not change. -/
def changeTargetFamilyEquiv (a : U ≅ V) (c : FiniteCover U) :
    CompatibleFamily c Y ≃ CompatibleFamily (changeTarget a c) Y :=
  Equiv.refl _

theorem changeTargetFamilyEquiv_gluingEquiv (a : U ≅ V) (c : FiniteCover U)
    (p : C(U.locus, Y)) :
    changeTargetFamilyEquiv a c (c.gluingEquiv p) =
      (changeTarget a c).gluingEquiv (p.comp a.inv.locusMap) := by
  apply Subtype.ext
  funext i
  apply ContinuousMap.ext
  intro x
  rfl

/-- The actual quotient glue changes only by precomposition on its target. -/
theorem glue_changeTargetFamily (a : U ≅ V) (c : FiniteCover U)
    (p : CompatibleFamily c Y) :
    (changeTarget a c).glue p.val p.property =
      (c.glue p.val p.property).comp a.inv.locusMap := by
  symm
  apply (changeTarget a c).glue_unique p.val p.property
  intro i
  change c.restrict (c.glue p.val p.property) i = p.val i
  exact c.restrict_glue p.val p.property i

/-- A refinement after target restoration identifies the original quotient
glue with the coarser glue pulled back along the actual target comparison. -/
theorem glue_changeTarget_pullback (a : U ≅ V)
    {b : FiniteCover U} {c : FiniteCover V}
    (r : Refinement (changeTarget a b) c) (p : CompatibleFamily c Y) :
    b.glue (r.pullback p).val (r.pullback p).property =
      (c.glue p.val p.property).comp a.hom.locusMap := by
  have hr := r.glue_pullbackFamily p.val p.property
  have ha := glue_changeTargetFamily a b (r.pullback p)
  have heq := ha.symm.trans hr
  apply ContinuousMap.ext
  intro x
  exact DFunLike.congr_fun heq (a.hom.locusMap x)

end Domain.FiniteCover

namespace RationalChart

open Domain.FiniteCover

variable {d e h j : RationalChart K A}
variable {Y : Type v} [TopologicalSpace Y]

/-- Restore the identity-transported target before comparing covers. -/
def nestedFiniteCoverIdIso (d : RationalChart K A) {U : Domain K d.algebra}
    (c : Domain.FiniteCover U) :
    changeTarget (nestedDomainIdIso d U) (nestedFiniteCover (𝟙 d) c) ≅ c where
  hom := {
    index := id
    map i := (nestedDomainIdIso d (c.obj i)).hom }
  inv := {
    index := id
    map i := (nestedDomainIdIso d (c.obj i)).inv }
  hom_inv_id := Refinement.ext rfl
  inv_hom_id := Refinement.ext rfl

/-- Restore the composite target before comparing successive transport with
direct transport. All component comparisons are actual identity bounded maps. -/
def nestedFiniteCoverCompIso (f : d ⟶ e) (g : e ⟶ h)
    {U : Domain K d.algebra} (c : Domain.FiniteCover U) :
    changeTarget (nestedDomainCompIso f g U)
        (nestedFiniteCover g (nestedFiniteCover f c)) ≅
      nestedFiniteCover (f ≫ g) c where
  hom := {
    index := id
    map i := (nestedDomainCompIso f g (c.obj i)).hom }
  inv := {
    index := id
    map i := (nestedDomainCompIso f g (c.obj i)).inv }
  hom_inv_id := Refinement.ext rfl
  inv_hom_id := Refinement.ext rfl

@[simp] theorem nestedFiniteCoverIdIso_hom_index (d : RationalChart K A)
    {U : Domain K d.algebra} (c : Domain.FiniteCover U) :
    (nestedFiniteCoverIdIso d c).hom.index = id := rfl

@[simp] theorem nestedFiniteCoverIdIso_inv_index (d : RationalChart K A)
    {U : Domain K d.algebra} (c : Domain.FiniteCover U) :
    (nestedFiniteCoverIdIso d c).inv.index = id := rfl

@[simp] theorem nestedFiniteCoverCompIso_hom_index (f : d ⟶ e) (g : e ⟶ h)
    {U : Domain K d.algebra} (c : Domain.FiniteCover U) :
    (nestedFiniteCoverCompIso f g c).hom.index = id := rfl

@[simp] theorem nestedFiniteCoverCompIso_inv_index (f : d ⟶ e) (g : e ⟶ h)
    {U : Domain K d.algebra} (c : Domain.FiniteCover U) :
    (nestedFiniteCoverCompIso f g c).inv.index = id := rfl

@[simp] theorem nestedFiniteCoverIdIso_hom_map_restriction (d : RationalChart K A)
    {U : Domain K d.algebra} (c : Domain.FiniteCover U) (i : Fin c.size) :
    ((nestedFiniteCoverIdIso d c).hom.map i).restriction =
      BoundedAlgHom.id K (c.obj i).algebra := rfl

@[simp] theorem nestedFiniteCoverIdIso_inv_map_restriction (d : RationalChart K A)
    {U : Domain K d.algebra} (c : Domain.FiniteCover U) (i : Fin c.size) :
    ((nestedFiniteCoverIdIso d c).inv.map i).restriction =
      BoundedAlgHom.id K (c.obj i).algebra := rfl

@[simp] theorem nestedFiniteCoverCompIso_hom_map_restriction
    (f : d ⟶ e) (g : e ⟶ h) {U : Domain K d.algebra}
    (c : Domain.FiniteCover U) (i : Fin c.size) :
    ((nestedFiniteCoverCompIso f g c).hom.map i).restriction =
      BoundedAlgHom.id K (c.obj i).algebra := rfl

@[simp] theorem nestedFiniteCoverCompIso_inv_map_restriction
    (f : d ⟶ e) (g : e ⟶ h) {U : Domain K d.algebra}
    (c : Domain.FiniteCover U) (i : Fin c.size) :
    ((nestedFiniteCoverCompIso f g c).inv.map i).restriction =
      BoundedAlgHom.id K (c.obj i).algebra := rfl

/-- The identity comparison is the identity on the retained disjoint union
of actual component spectra. -/
theorem nestedFiniteCoverIdIso_hom_spectrumMap (d : RationalChart K A)
    {U : Domain K d.algebra} (c : Domain.FiniteCover U) :
    (nestedFiniteCoverIdIso d c).hom.spectrumMap =
      ContinuousMap.id (Σ i : Fin c.size, BanachSpectrum (c.obj i).algebra) := by
  apply ContinuousMap.ext
  rintro ⟨i, x⟩
  exact congrArg (Sigma.mk i) (BanachSpectrum.ext (fun a => rfl))

/-- The composition comparison also retains every actual spectrum point. -/
theorem nestedFiniteCoverCompIso_hom_spectrumMap (f : d ⟶ e) (g : e ⟶ h)
    {U : Domain K d.algebra} (c : Domain.FiniteCover U) :
    (nestedFiniteCoverCompIso f g c).hom.spectrumMap =
      ContinuousMap.id (Σ i : Fin c.size, BanachSpectrum (c.obj i).algebra) := by
  apply ContinuousMap.ext
  rintro ⟨i, x⟩
  exact congrArg (Sigma.mk i) (BanachSpectrum.ext (fun a => rfl))

def nestedFiniteCoverIdNatIso (d : RationalChart K A) (U : Domain K d.algebra) :
    nestedFiniteCoverFunctor (𝟙 d) U ⋙ changeTargetFunctor (nestedDomainIdIso d U) ≅
      𝟭 (Domain.FiniteCover U) :=
  NatIso.ofComponents (nestedFiniteCoverIdIso d)
    (by intro b c r; exact Refinement.ext rfl)

def nestedFiniteCoverCompNatIso (f : d ⟶ e) (g : e ⟶ h)
    (U : Domain K d.algebra) :
    nestedFiniteCoverFunctor f U ⋙
        nestedFiniteCoverFunctor g (nestedDomain f U) ⋙
        changeTargetFunctor (nestedDomainCompIso f g U) ≅
      nestedFiniteCoverFunctor (f ≫ g) U :=
  NatIso.ofComponents (nestedFiniteCoverCompIso f g)
    (by intro b c r; exact Refinement.ext rfl)

/-- The unit and associativity comparisons agree on every actual component,
with identity chosen indices as exposed above. -/
theorem nestedFiniteCoverCompIso_source_id_map (f : d ⟶ e)
    {U : Domain K d.algebra} (c : Domain.FiniteCover U) (i : Fin c.size) :
    (nestedFiniteCoverCompIso (𝟙 d) f c).hom.map i =
      (nestedDomainFunctor f).map ((nestedFiniteCoverIdIso d c).hom.map i) :=
  nestedDomainCompIso_source_id f (c.obj i)

theorem nestedFiniteCoverCompIso_target_id_map (f : d ⟶ e)
    {U : Domain K d.algebra} (c : Domain.FiniteCover U) (i : Fin c.size) :
    (nestedFiniteCoverCompIso f (𝟙 e) c).hom.map i =
      (nestedFiniteCoverIdIso e (nestedFiniteCover f c)).hom.map i :=
  nestedDomainCompIso_target_id f (c.obj i)

theorem nestedFiniteCoverCompIso_assoc_map (f : d ⟶ e) (g : e ⟶ h) (k : h ⟶ j)
    {U : Domain K d.algebra} (c : Domain.FiniteCover U) (i : Fin c.size) :
    (nestedDomainFunctor k).map ((nestedFiniteCoverCompIso f g c).hom.map i) ≫
        (nestedFiniteCoverCompIso (f ≫ g) k c).hom.map i =
      (nestedFiniteCoverCompIso g k (nestedFiniteCover f c)).hom.map i ≫
        (nestedFiniteCoverCompIso f (g ≫ k) c).hom.map i :=
  nestedDomainCompIso_assoc f g k (c.obj i)

/-- The inverse identity homeomorphism is the actual domain comparison. -/
theorem nestedDomainLocusHomeomorph_symm_id (d : RationalChart K A)
    (U : Domain K d.algebra) (x : (nestedDomain (𝟙 d) U).locus) :
    (nestedDomainLocusHomeomorph (𝟙 d) U).symm x =
      (nestedDomainIdIso d U).hom.locusMap x := by
  exact (nestedDomainLocusHomeomorph_id d U
    ((nestedDomainLocusHomeomorph (𝟙 d) U).symm x)).symm.trans
      (congrArg (nestedDomainIdIso d U).hom.locusMap
        ((nestedDomainLocusHomeomorph (𝟙 d) U).apply_symm_apply x))

/-- Inverse target comparisons obey composition on actual spectrum points. -/
theorem nestedDomainLocusHomeomorph_symm_comp (f : d ⟶ e) (g : e ⟶ h)
    (U : Domain K d.algebra) (x : (nestedDomain g (nestedDomain f U)).locus) :
    (nestedDomainLocusHomeomorph (f ≫ g) U).symm
        ((nestedDomainCompIso f g U).hom.locusMap x) =
      (nestedDomainLocusHomeomorph f U).symm
        ((nestedDomainLocusHomeomorph g (nestedDomain f U)).symm x) := by
  let y := (nestedDomainLocusHomeomorph f U).symm
    ((nestedDomainLocusHomeomorph g (nestedDomain f U)).symm x)
  have hf : nestedDomainLocusHomeomorph f U y =
      (nestedDomainLocusHomeomorph g (nestedDomain f U)).symm x :=
    (nestedDomainLocusHomeomorph f U).apply_symm_apply _
  have hg : nestedDomainLocusHomeomorph g (nestedDomain f U)
      (nestedDomainLocusHomeomorph f U y) = x :=
    (congrArg (nestedDomainLocusHomeomorph g (nestedDomain f U)) hf).trans
      ((nestedDomainLocusHomeomorph g (nestedDomain f U)).apply_symm_apply x)
  have hc := nestedDomainLocusHomeomorph_comp f g U y
  apply (nestedDomainLocusHomeomorph (f ≫ g) U).injective
  rw [Homeomorph.apply_symm_apply]
  exact (congrArg (nestedDomainCompIso f g U).hom.locusMap hg).symm.trans hc

/-- Identity family transport is pullback through the actual cover comparison. -/
theorem nestedCoverFamilyEquiv_id (d : RationalChart K A)
    {U : Domain K d.algebra} (c : Domain.FiniteCover U) (p : CompatibleFamily c Y) :
    nestedCoverFamilyEquiv (𝟙 d) c p =
      (nestedFiniteCoverIdIso d c).hom.pullback p := by
  apply Subtype.ext
  funext i
  apply ContinuousMap.ext
  intro x
  exact congrArg (p.val i) (nestedDomainLocusHomeomorph_symm_id d (c.obj i) x)

/-- Successive family transport agrees with direct transport pulled back
through the specified actual composite-cover comparison. -/
theorem nestedCoverFamilyEquiv_comp (f : d ⟶ e) (g : e ⟶ h)
    {U : Domain K d.algebra} (c : Domain.FiniteCover U) (p : CompatibleFamily c Y) :
    nestedCoverFamilyEquiv g (nestedFiniteCover f c) (nestedCoverFamilyEquiv f c p) =
      (nestedFiniteCoverCompIso f g c).hom.pullback
        (nestedCoverFamilyEquiv (f ≫ g) c p) := by
  apply Subtype.ext
  funext i
  apply ContinuousMap.ext
  intro x
  exact congrArg (p.val i) (nestedDomainLocusHomeomorph_symm_comp f g (c.obj i) x).symm

/-- Identity transport preserves the actual quotient glue after the specified
target comparison. -/
theorem glue_nestedCoverFamily_id (d : RationalChart K A)
    {U : Domain K d.algebra} (c : Domain.FiniteCover U) (p : CompatibleFamily c Y) :
    (nestedFiniteCover (𝟙 d) c).glue (nestedCoverFamilyEquiv (𝟙 d) c p).val
        (nestedCoverFamilyEquiv (𝟙 d) c p).property =
      (c.glue p.val p.property).comp (nestedDomainIdIso d U).hom.locusMap := by
  let r := (nestedFiniteCoverIdIso d c).hom
  have hp : nestedCoverFamilyEquiv (𝟙 d) c p = r.pullback p :=
    nestedCoverFamilyEquiv_id d c p
  exact (congrArg (fun q : CompatibleFamily (nestedFiniteCover (𝟙 d) c) Y =>
    (nestedFiniteCover (𝟙 d) c).glue q.val q.property) hp).trans
      (glue_changeTarget_pullback (nestedDomainIdIso d U) r p)

/-- Successive and direct transport have the same actual quotient glue,
with the composite-domain comparison made explicit. -/
theorem glue_nestedCoverFamily_comp (f : d ⟶ e) (g : e ⟶ h)
    {U : Domain K d.algebra} (c : Domain.FiniteCover U) (p : CompatibleFamily c Y) :
    (nestedFiniteCover g (nestedFiniteCover f c)).glue
        (nestedCoverFamilyEquiv g (nestedFiniteCover f c)
          (nestedCoverFamilyEquiv f c p)).val
        (nestedCoverFamilyEquiv g (nestedFiniteCover f c)
          (nestedCoverFamilyEquiv f c p)).property =
      ((nestedFiniteCover (f ≫ g) c).glue (nestedCoverFamilyEquiv (f ≫ g) c p).val
        (nestedCoverFamilyEquiv (f ≫ g) c p).property).comp
          (nestedDomainCompIso f g U).hom.locusMap := by
  let r := (nestedFiniteCoverCompIso f g c).hom
  let q := nestedCoverFamilyEquiv (f ≫ g) c p
  have hp : nestedCoverFamilyEquiv g (nestedFiniteCover f c)
      (nestedCoverFamilyEquiv f c p) = r.pullback q :=
    nestedCoverFamilyEquiv_comp f g c p
  exact (congrArg
    (fun s : CompatibleFamily (nestedFiniteCover g (nestedFiniteCover f c)) Y =>
      (nestedFiniteCover g (nestedFiniteCover f c)).glue s.val s.property) hp).trans
        (glue_changeTarget_pullback (nestedDomainCompIso f g U) r q)

end RationalChart
end Langlands.Analytic.PresentedAffinoidAlgebra
