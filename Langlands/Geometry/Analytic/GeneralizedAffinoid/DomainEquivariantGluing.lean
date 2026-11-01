import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainFiniteInvariantCover
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainGluing

/-! # Equivariant continuous gluing on finite represented-domain covers -/

noncomputable section

universe u v w

namespace Langlands.Analytic.PresentedAffinoidAlgebra.DomainAutomorphism.DomainSpectralAction

open CategoryTheory

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {P : PresentedAffinoidAlgebra K}
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (ρ : DomainSpectralAction G P)

/-- The pointwise equivariance equation, allowing an independent target universe. -/
def LocusEquivariant (H : OpenSubgroup G) (d : ρ.InvariantDomain H)
    (Y : Action TopCat.{w} H) (f : C(d.obj.locus, Y.V)) : Prop :=
  ∀ (g : H) (x : d.obj.locus),
    f (ρ.invariantLocusOperator H d g x) = ConcreteCategory.hom (Y.ρ g) (f x)

/-- Actual continuous equivariant maps out of a represented locus. -/
abbrev EquivariantLocusMap (H : OpenSubgroup G) (d : ρ.InvariantDomain H)
    (Y : Action TopCat.{w} H) :=
  {f : C(d.obj.locus, Y.V) // ρ.LocusEquivariant H d Y f}

/-- In one universe these are exactly the morphisms of Mathlib's action category. -/
def equivariantLocusMapHomEquiv (H : OpenSubgroup G) (d : ρ.InvariantDomain H)
    (Y : Action TopCat.{u} H) :
    (ρ.invariantLocusAction H d ⟶ Y) ≃ ρ.EquivariantLocusMap H d Y where
  toFun f := ⟨f.hom.hom, fun g x => ConcreteCategory.congr_hom (f.comm g) x⟩
  invFun f :=
    { hom := TopCat.ofHom f.val
      comm := fun g => by
        apply TopCat.ext
        intro x
        exact f.property g x }
  left_inv _ := Action.Hom.ext rfl
  right_inv _ := Subtype.ext rfl

variable (H : OpenSubgroup G) (d : ρ.InvariantDomain H) (c : Domain.FiniteCover d.obj)

/-- Each original bounded cover arrow induces its equivariant locus inclusion. -/
def finiteCoverLocusInclusion (i : Fin c.size) :
    ρ.invariantLocusAction (ρ.finiteFamilyOpenSubgroup H c.obj)
        (ρ.finiteInvariantFamily H c.obj i) ⟶
      ρ.invariantLocusAction (ρ.finiteFamilyOpenSubgroup H c.obj)
        (ρ.finiteInvariantTarget H d c.obj) :=
  (ρ.invariantLocusActionFunctor (ρ.finiteFamilyOpenSubgroup H c.obj)).map
    (ρ.finiteInvariantFamilyArrow H d c.obj c.map i)

@[simp]
theorem finiteCoverLocusInclusion_apply (i : Fin c.size) (x : (c.obj i).locus) :
    (ρ.finiteCoverLocusInclusion H d c i).hom x = (c.map i).locusMap x :=
  rfl

variable (Y : Action TopCat.{w} (ρ.finiteFamilyOpenSubgroup H c.obj))

/-- Equivariance is detected on the original component loci of the cover. -/
theorem finiteCoverEquivariant_iff (f : C(d.obj.locus, Y.V)) :
    ρ.LocusEquivariant (ρ.finiteFamilyOpenSubgroup H c.obj)
        (ρ.finiteInvariantTarget H d c.obj) Y f ↔
      ∀ i, ρ.LocusEquivariant (ρ.finiteFamilyOpenSubgroup H c.obj)
        (ρ.finiteInvariantFamily H c.obj i) Y (c.restrict f i) := by
  constructor
  · intro hf i g x
    exact hf g ((c.map i).locusMap x)
  · intro hf g x
    obtain ⟨i, hi⟩ := c.covers x.val x.property
    exact hf i g ⟨x.val, hi⟩

/-- Compatible equivariant continuous maps on the unchanged component loci. -/
abbrev FiniteCoverEquivariantFamily :=
  {g : ∀ i : Fin c.size,
      ρ.EquivariantLocusMap (ρ.finiteFamilyOpenSubgroup H c.obj)
        (ρ.finiteInvariantFamily H c.obj i) Y //
    c.Compatible (fun i => (g i).val)}

/-- Restrict an equivariant continuous map through the original bounded cover. -/
def finiteCoverRestrict
    (f : ρ.EquivariantLocusMap (ρ.finiteFamilyOpenSubgroup H c.obj)
      (ρ.finiteInvariantTarget H d c.obj) Y) :
    ρ.FiniteCoverEquivariantFamily H d c Y :=
  ⟨fun i => ⟨c.restrict f.val i,
    (ρ.finiteCoverEquivariant_iff H d c Y f.val).mp f.property i⟩,
    c.compatible_restrict f.val⟩

/-- Descend through the actual finite spectrum quotient, then prove equivariance
by the component restriction identities. -/
def finiteCoverGlue (g : ρ.FiniteCoverEquivariantFamily H d c Y) :
    ρ.EquivariantLocusMap (ρ.finiteFamilyOpenSubgroup H c.obj)
      (ρ.finiteInvariantTarget H d c.obj) Y :=
  ⟨c.glue (fun i => (g.val i).val) g.property,
    (ρ.finiteCoverEquivariant_iff H d c Y _).mpr (by
      intro i
      exact Eq.mpr
        (congrArg (ρ.LocusEquivariant (ρ.finiteFamilyOpenSubgroup H c.obj)
          (ρ.finiteInvariantFamily H c.obj i) Y)
          (c.restrict_glue (fun i => (g.val i).val) g.property i))
        (g.val i).property)⟩

theorem finiteCoverGlue_apply_spectrum
    (g : ρ.FiniteCoverEquivariantFamily H d c Y) (i : Fin c.size)
    (x : BanachSpectrum (c.obj i).algebra) :
    (ρ.finiteCoverGlue H d c Y g).val (c.componentMap i x) =
      (g.val i).val ((c.obj i).spectrumToLocus x) :=
  c.glue_apply_spectrum (fun i => (g.val i).val) g.property i x

@[simp]
theorem finiteCoverRestrict_glue (g : ρ.FiniteCoverEquivariantFamily H d c Y) :
    ρ.finiteCoverRestrict H d c Y (ρ.finiteCoverGlue H d c Y g) = g := by
  apply Subtype.ext
  funext i
  apply Subtype.ext
  exact c.restrict_glue (fun i => (g.val i).val) g.property i

@[simp]
theorem finiteCoverGlue_restrict
    (f : ρ.EquivariantLocusMap (ρ.finiteFamilyOpenSubgroup H c.obj)
      (ρ.finiteInvariantTarget H d c.obj) Y) :
    ρ.finiteCoverGlue H d c Y (ρ.finiteCoverRestrict H d c Y f) = f := by
  apply Subtype.ext
  exact c.glue_restrict f.val

/-- Equivariant maps on the target are exactly compatible equivariant families. -/
def finiteCoverGluingEquiv :
    ρ.EquivariantLocusMap (ρ.finiteFamilyOpenSubgroup H c.obj)
        (ρ.finiteInvariantTarget H d c.obj) Y ≃
      ρ.FiniteCoverEquivariantFamily H d c Y where
  toFun := ρ.finiteCoverRestrict H d c Y
  invFun := ρ.finiteCoverGlue H d c Y
  left_inv := ρ.finiteCoverGlue_restrict H d c Y
  right_inv := ρ.finiteCoverRestrict_glue H d c Y

theorem finiteCoverGlue_unique
    (g : ρ.FiniteCoverEquivariantFamily H d c Y)
    (f : ρ.EquivariantLocusMap (ρ.finiteFamilyOpenSubgroup H c.obj)
      (ρ.finiteInvariantTarget H d c.obj) Y)
    (hf : ∀ i, c.restrict f.val i = (g.val i).val) :
    f = ρ.finiteCoverGlue H d c Y g := by
  apply Subtype.ext
  exact c.glue_unique (fun i => (g.val i).val) g.property f.val hf

/-- Postcompose with an actual equivariant morphism of target spaces. -/
def equivariantLocusMapPostcomp {J : OpenSubgroup G} {e : ρ.InvariantDomain J}
    {Y Z : Action TopCat.{w} J} (p : Y ⟶ Z) (f : ρ.EquivariantLocusMap J e Y) :
    ρ.EquivariantLocusMap J e Z :=
  ⟨p.hom.hom.comp f.val, fun g x => by
    change p.hom (f.val (ρ.invariantLocusOperator J e g x)) =
      ConcreteCategory.hom (Z.ρ g) (p.hom (f.val x))
    rw [f.property g x]
    exact ConcreteCategory.congr_hom (p.comm g) (f.val x)⟩

variable {Y} {Z : Action TopCat.{w} (ρ.finiteFamilyOpenSubgroup H c.obj)}

def finiteCoverFamilyPostcomp (p : Y ⟶ Z)
    (g : ρ.FiniteCoverEquivariantFamily H d c Y) :
    ρ.FiniteCoverEquivariantFamily H d c Z :=
  ⟨fun i => ρ.equivariantLocusMapPostcomp p (g.val i),
    c.compatible_postcomp _ g.property p.hom.hom⟩

/-- Restriction commutes with equivariant postcomposition. -/
theorem finiteCoverRestrict_postcomp (p : Y ⟶ Z)
    (f : ρ.EquivariantLocusMap (ρ.finiteFamilyOpenSubgroup H c.obj)
      (ρ.finiteInvariantTarget H d c.obj) Y) :
    ρ.finiteCoverRestrict H d c Z (ρ.equivariantLocusMapPostcomp p f) =
      ρ.finiteCoverFamilyPostcomp H d c p (ρ.finiteCoverRestrict H d c Y f) := by
  apply Subtype.ext
  funext i
  apply Subtype.ext
  rfl

/-- The quotient-lift gluing commutes with equivariant postcomposition. -/
theorem finiteCoverGlue_postcomp (p : Y ⟶ Z)
    (g : ρ.FiniteCoverEquivariantFamily H d c Y) :
    ρ.equivariantLocusMapPostcomp p (ρ.finiteCoverGlue H d c Y g) =
      ρ.finiteCoverGlue H d c Z (ρ.finiteCoverFamilyPostcomp H d c p g) := by
  apply Subtype.ext
  exact c.glue_postcomp _ g.property p.hom.hom

variable (Y : Action TopCat.{u} (ρ.finiteFamilyOpenSubgroup H c.obj))

/-- Compatible families of ordinary morphisms in the action category. -/
abbrev FiniteCoverCompatibleHomFamily :=
  {g : ∀ i : Fin c.size,
      ρ.invariantLocusAction (ρ.finiteFamilyOpenSubgroup H c.obj)
        (ρ.finiteInvariantFamily H c.obj i) ⟶ Y //
    c.Compatible (fun i => (g i).hom.hom)}

/-- The independent-universe description retains exactly the categorical
morphisms when source and target universes agree. -/
def finiteCoverHomFamilyEquiv :
    ρ.FiniteCoverCompatibleHomFamily H d c Y ≃
      ρ.FiniteCoverEquivariantFamily H d c Y where
  toFun g := ⟨fun i => ρ.equivariantLocusMapHomEquiv _ _ Y (g.val i), g.property⟩
  invFun g :=
    ⟨fun i => (ρ.equivariantLocusMapHomEquiv _ _ Y).symm (g.val i), g.property⟩
  left_inv g := by
    apply Subtype.ext
    funext i
    exact (ρ.equivariantLocusMapHomEquiv _ _ Y).symm_apply_apply (g.val i)
  right_inv g := by
    apply Subtype.ext
    funext i
    exact (ρ.equivariantLocusMapHomEquiv _ _ Y).apply_symm_apply (g.val i)

/-- Actual equivariant morphisms glue uniquely from compatible component
morphisms, retaining the quotient-lift inverse. -/
def finiteCoverHomGluingEquiv :
    (ρ.invariantLocusAction (ρ.finiteFamilyOpenSubgroup H c.obj)
        (ρ.finiteInvariantTarget H d c.obj) ⟶ Y) ≃
      ρ.FiniteCoverCompatibleHomFamily H d c Y :=
  ((ρ.equivariantLocusMapHomEquiv _ _ Y).trans
    (ρ.finiteCoverGluingEquiv H d c Y)).trans
      (ρ.finiteCoverHomFamilyEquiv H d c Y).symm

@[simp]
theorem finiteCoverHomGluingEquiv_apply
    (f : ρ.invariantLocusAction (ρ.finiteFamilyOpenSubgroup H c.obj)
      (ρ.finiteInvariantTarget H d c.obj) ⟶ Y) (i : Fin c.size) :
    (ρ.finiteCoverHomGluingEquiv H d c Y f).val i =
      ρ.finiteCoverLocusInclusion H d c i ≫ f :=
  Action.Hom.ext rfl

@[simp]
theorem finiteCoverHomGluingEquiv_symm_hom
    (g : ρ.FiniteCoverCompatibleHomFamily H d c Y) :
    ((ρ.finiteCoverHomGluingEquiv H d c Y).symm g).hom =
      TopCat.ofHom (c.glue (fun i => (g.val i).hom.hom) g.property) :=
  rfl

end Langlands.Analytic.PresentedAffinoidAlgebra.DomainAutomorphism.DomainSpectralAction
