import Langlands.GroupScheme.RelativeIdentityComponent.SmoothProof
import Langlands.AbelianScheme.KernelBaseChange

/-! # Sections near a point of the relative identity component -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeIdentityComponent

open Langlands.AlgebraicGeometry

section Smooth

variable {S : Scheme.{u}} (G : GroupScheme S) [Smooth G.X.hom]

/-- The relative identity set of a smooth group is open. -/
theorem isOpen_underlyingSet : IsOpen (underlyingSet G) := by
  obtain ⟨H, i, hi, -, -⟩ := smoothStructure.1 S G inferInstance
  rw [← hi.range_eq_underlyingSet]
  let : IsOpenImmersion i.hom.hom.left := hi.isOpenImmersion
  exact IsOpenImmersion.isOpen_range _

/-- The open locus on which a map lands in the relative identity component. -/
def sectionIdentityOpen (g : S ⟶ G.X.left) : S.Opens :=
  ⟨g ⁻¹' underlyingSet G, (isOpen_underlyingSet G).preimage g.continuous⟩

/-- For a section, membership in this open is membership of its actual residue
fibre point in the identity component. -/
theorem mem_sectionIdentityOpen_iff (g : S ⟶ G.X.left)
    (hg : g ≫ G.X.hom = 𝟙 S) (s : S) :
    s ∈ sectionIdentityOpen G g ↔
      SectionComponent.fiberPoint G.X.hom g hg s ∈
        IdentityComponent.identitySet (residueFiber G s) := by
  change g s ∈ underlyingSet G ↔ _
  simpa only [SectionComponent.fiberι_fiberPoint] using
    fiberι_mem_underlyingSet_iff G s (SectionComponent.fiberPoint G.X.hom g hg s)

/-- An actual open neighbourhood and a lift of the restricted section to a
geometrically connected representative of the relative identity component. -/
structure SectionIdentityNeighbourhoodData (g : S ⟶ G.X.left) (s : S) where
  neighbourhood : S.Opens
  mem_neighbourhood : s ∈ neighbourhood
  component : GroupScheme S
  inclusion : component ⟶ G
  represents : IsRelativeIdentityComponent G inclusion
  geometricallyConnected : GeometricallyConnected component.X.hom
  sectionLift : Over.mk neighbourhood.ι ⟶ component.X
  recovers : sectionLift.left ≫ inclusion.hom.hom.left = neighbourhood.ι ≫ g

/-- A section whose specified residue-fibre point lies in the identity
component lifts to the relative identity component on an open neighbourhood. -/
theorem exists_section_identity_neighbourhood (g : S ⟶ G.X.left)
    (hg : g ≫ G.X.hom = 𝟙 S) (s : S)
    (hs : SectionComponent.fiberPoint G.X.hom g hg s ∈
      IdentityComponent.identitySet (residueFiber G s)) :
    Nonempty (SectionIdentityNeighbourhoodData G g s) := by
  obtain ⟨H, i, hi, -, hconn⟩ := smoothStructure.1 S G inferInstance
  let U := sectionIdentityOpen G g
  let a : Over.mk U.ι ⟶ G.X :=
    Over.homMk (U.ι ≫ g) (by simp [Category.assoc, hg])
  have ha : Set.range a.left ⊆ underlyingSet G := by
    rintro _ ⟨t, rfl⟩
    exact t.property
  obtain ⟨b, hb⟩ := (factors_iff_range_subset G hi _ a).mpr ha
  exact ⟨⟨U, (mem_sectionIdentityOpen_iff G g hg s).mpr hs,
    H, i, hi, hconn, b, congrArg (fun f => f.left) hb⟩⟩

/-- Choose actual neighbourhood and section-lift data. -/
def sectionIdentityNeighbourhood (g : S ⟶ G.X.left)
    (hg : g ≫ G.X.hom = 𝟙 S) (s : S)
    (hs : SectionComponent.fiberPoint G.X.hom g hg s ∈
      IdentityComponent.identitySet (residueFiber G s)) :
    SectionIdentityNeighbourhoodData G g s :=
  Classical.choice (exists_section_identity_neighbourhood G g hg s hs)

end Smooth

namespace SectionIdentityNeighbourhoodData

variable {S : Scheme.{u}} {G : GroupScheme S} {g : S ⟶ G.X.left} {s : S}
  (d : SectionIdentityNeighbourhoodData G g s)
  (hg : g ≫ G.X.hom = 𝟙 S)
  {K : Type u} [Field K] (q : Spec (CommRingCat.of K) ⟶ S)

/-- The section induces an actual rational point of its pullback along any
field-valued base point. -/
def fieldSection (_d : SectionIdentityNeighbourhoodData G g s) :
    𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ ((GroupScheme.baseChange q).obj G).X :=
  (baseChangePointsEquiv q G _).symm
    (Over.homMk (q ≫ g) (by simp [Category.assoc, hg]))

@[reassoc]
theorem fieldSection_recovers :
    (d.fieldSection hg q).left ≫ pullback.fst G.X.hom q = q ≫ g := by
  change (baseChangePointsEquiv q G _ (d.fieldSection hg q)).left = _
  exact congrArg (fun f => f.left) ((baseChangePointsEquiv q G _).apply_symm_apply _)

/-- Pull the actual lifted section back at a field point contained in the
chosen neighbourhood. -/
def fieldLift (hq : Set.range q ⊆ (d.neighbourhood : Set S)) :
    𝟙_ (Over (Spec (CommRingCat.of K))) ⟶
      ((GroupScheme.baseChange q).obj d.component).X := by
  have hr : Set.range q ⊆ Set.range d.neighbourhood.ι := by
    rwa [Scheme.Opens.range_ι]
  let b := IsOpenImmersion.lift d.neighbourhood.ι q hr
  have hb : b ≫ d.neighbourhood.ι = q := IsOpenImmersion.lift_fac _ _ _
  exact (baseChangePointsEquiv q d.component _).symm
    (Over.homMk (b ≫ d.sectionLift.left) (by
      rw [Category.assoc, Over.w d.sectionLift]
      change b ≫ d.neighbourhood.ι = 𝟙 _ ≫ q
      simpa using hb))

@[reassoc]
theorem fieldLift_comp (hq : Set.range q ⊆ (d.neighbourhood : Set S)) :
    d.fieldLift q hq ≫ ((GroupScheme.baseChange q).map d.inclusion).hom.hom =
      d.fieldSection hg q := by
  apply (baseChangePointsEquiv q G _).injective
  rw [baseChangePointsEquiv_comp]
  change (baseChangePointsEquiv q d.component _ _ ≫ d.inclusion.hom.hom) = _
  simp only [fieldLift, fieldSection, MulEquiv.apply_symm_apply]
  apply Over.OverMorphism.ext
  change (IsOpenImmersion.lift d.neighbourhood.ι q _ ≫ d.sectionLift.left) ≫
    d.inclusion.hom.hom.left = q ≫ g
  rw [Category.assoc, d.recovers, ← Category.assoc, IsOpenImmersion.lift_fac]

/-- Every such field point lies in the actual fibre identity component.
No affineness or connectedness of the ambient group is needed here. -/
theorem range_fieldSection_subset_identitySet
    (hq : Set.range q ⊆ (d.neighbourhood : Set S)) :
    Set.range (d.fieldSection hg q).left ⊆
      IdentityComponent.identitySet ((GroupScheme.baseChange q).obj G) := by
  let : GeometricallyConnected d.component.X.hom := d.geometricallyConnected
  let : GeometricallyConnected ((GroupScheme.baseChange q).obj d.component).X.hom :=
    inferInstanceAs (GeometricallyConnected (pullback.snd d.component.X.hom q))
  let : ConnectedSpace ((GroupScheme.baseChange q).obj d.component).X.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton
      (f := ((GroupScheme.baseChange q).obj d.component).X.hom)
  have hr := IdentityComponent.range_subset_identitySet
    ((GroupScheme.baseChange q).obj G)
    ((GroupScheme.baseChange q).map d.inclusion).hom.hom
    η[((GroupScheme.baseChange q).obj d.component).X] (IsMonHom.one_hom _)
  rw [← d.fieldLift_comp hg q hq]
  rintro _ ⟨t, rfl⟩
  exact hr ⟨(d.fieldLift q hq).left t, rfl⟩

instance fieldGroup_smooth [Smooth G.X.hom] :
    Smooth ((GroupScheme.baseChange q).obj G).X.hom :=
  inferInstanceAs (Smooth (pullback.snd G.X.hom q))

instance fieldGroup_isAffineHom [IsAffineHom G.X.hom] :
    IsAffineHom ((GroupScheme.baseChange q).obj G).X.hom :=
  inferInstanceAs (IsAffineHom (pullback.snd G.X.hom q))

variable [Smooth G.X.hom] [IsAffineHom G.X.hom]

/-- The actual factor point in the actual identity-component group of the
field pullback. -/
def fieldIdentityPoint (hq : Set.range q ⊆ (d.neighbourhood : Set S)) :
    𝟙_ (Over (Spec (CommRingCat.of K))) ⟶
      (identityComponent ((GroupScheme.baseChange q).obj G)).X :=
  FiniteEtaleImage.liftOver
    (identityComponentι ((GroupScheme.baseChange q).obj G)).hom.hom
    (d.fieldSection hg q) (by
      rw [IdentityComponent.range_identityComponentι]
      exact d.range_fieldSection_subset_identitySet hg q hq)

@[reassoc (attr := simp)]
theorem fieldIdentityPoint_comp (hq : Set.range q ⊆ (d.neighbourhood : Set S)) :
    d.fieldIdentityPoint hg q hq ≫
      (identityComponentι ((GroupScheme.baseChange q).obj G)).hom.hom =
        d.fieldSection hg q :=
  FiniteEtaleImage.liftOver_fac _ _ _

/-- Inclusion of the factor point and projection from the actual pullback
recover the original section as an equality of scheme morphisms. -/
@[reassoc]
theorem fieldIdentityPoint_recovers
    (hq : Set.range q ⊆ (d.neighbourhood : Set S)) :
    (d.fieldIdentityPoint hg q hq).left ≫
        (identityComponentι ((GroupScheme.baseChange q).obj G)).hom.hom.left ≫
        pullback.fst G.X.hom q = q ≫ g := by
  rw [← Category.assoc, ← Over.comp_left, d.fieldIdentityPoint_comp]
  exact d.fieldSection_recovers hg q

variable (t : S) (ht : t ∈ d.neighbourhood)

include ht in
omit [Smooth G.X.hom] [IsAffineHom G.X.hom] in
/-- The chosen geometric point over a point of the neighbourhood remains in it. -/
theorem range_geometricPoint_subset :
    Set.range (geometricPoint S t) ⊆ (d.neighbourhood : Set S) := by
  rintro _ ⟨x, rfl⟩
  change S.fromSpecResidueField t ((toAlgebraicClosure _) x) ∈ d.neighbourhood
  simpa only [Scheme.fromSpecResidueField_apply] using ht

/-- The actual point of the identity component of the original geometric fibre. -/
def geometricIdentityPoint :
    𝟙_ (Over (Spec (CommRingCat.of (AlgebraicClosure (S.residueField t))))) ⟶
      (identityComponent (geometricFiber G t)).X :=
  d.fieldIdentityPoint hg (geometricPoint S t) (d.range_geometricPoint_subset t ht)

/-- The geometric identity-component factor recovers the actual original
geometric section point. -/
@[reassoc]
theorem geometricIdentityPoint_recovers :
    (d.geometricIdentityPoint hg t ht).left ≫
        (identityComponentι (geometricFiber G t)).hom.hom.left ≫
        pullback.fst G.X.hom (geometricPoint S t) =
      geometricPoint S t ≫ g :=
  d.fieldIdentityPoint_recovers hg (geometricPoint S t)
    (d.range_geometricPoint_subset t ht)

end SectionIdentityNeighbourhoodData

end Langlands.GroupScheme.RelativeIdentityComponent
