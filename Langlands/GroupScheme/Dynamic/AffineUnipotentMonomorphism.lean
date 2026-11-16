import Langlands.GroupScheme.Dynamic.UnipotentMonomorphism
import Langlands.GroupScheme.Dynamic.AffineRepresentability

/-! # Relative unipotent monomorphisms with arbitrary affine representatives -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Corepresented.RelativeUnipotent

variable {R : CommRingCat.{u}}
  {F F' : CommAlgCat.{u} R ⥤ GrpCat.{u}} {B C : CommAlgCat.{u} R}
  {e : (F ⋙ forget GrpCat).CorepresentableBy B}
  {e' : (F' ⋙ forget GrpCat).CorepresentableBy C}
  (χ : (Gm (Spec R)).toGrp ⟶ groupScheme F e)
  (f : groupScheme F e ⟶ groupScheme F' e') [Mono f.hom.hom]
  {U V : GroupScheme (Spec R)} {i : U ⟶ groupScheme F e} {j : V ⟶ groupScheme F' e'}
  (hi : (Dynamic.unipotent χ).IsRepresentedBy i)
  (hj : (Dynamic.unipotent (χ ≫ f)).IsRepresentedBy j)

include χ hi hj in
/-- Closedness for any representatives of the two unipotent functors. -/
theorem isClosedSubgroup_of_represented (g : U ⟶ V) (hg : g ≫ j = i ≫ f) :
    IsClosedSubgroup g := by
  let α := hi.isoOfIsRepresentedBy (isRepresentedBy_unipotentHom χ)
  let β := hj.isoOfIsRepresentedBy (isRepresentedBy_unipotentHom (χ ≫ f))
  have hα : α.hom ≫ unipotentHom χ = i :=
    hi.isoOfIsRepresentedBy_hom_comp _
  have hβ : β.hom ≫ unipotentHom (χ ≫ f) = j :=
    hj.isoOfIsRepresentedBy_hom_comp _
  have h : g ≫ β.hom = α.hom ≫ unipotentMap χ f := by
    apply (isRepresentedBy_unipotentHom (χ ≫ f)).hom_ext
    rw [Category.assoc, hβ, hg, Category.assoc, unipotentMap_comp, ← Category.assoc, hα]
  apply (IsClosedSubgroup.comp_iso_iff g β).mp
  rw [h]
  exact (show IsClosedSubgroup (unipotentMap χ f) from
    isClosedImmersion_unipotentMap χ f).iso_comp α

end Langlands.GroupScheme.Corepresented.RelativeUnipotent

namespace Langlands.GroupScheme.Dynamic

variable {R : CommRingCat.{u}} {G H U V : GroupScheme (Spec R)}
  (χ : (Gm (Spec R)).toGrp ⟶ G) (f : G ⟶ H)
  {i : U ⟶ G} {j : V ⟶ H}
  (hi : (unipotent χ).IsRepresentedBy i)
  (hj : (unipotent (χ ≫ f)).IsRepresentedBy j)

set_option backward.isDefEq.respectTransparency false in
/-- The homomorphism on any representatives of the relative unipotent functors. -/
def unipotentFactor : U ⟶ V :=
  hj.factorHom (i ≫ f) (by
    rintro T _ ⟨x, rfl⟩
    change x ≫ (i.hom.hom ≫ f.hom.hom) ∈ (unipotent (χ ≫ f)).carrier T
    rw [← Category.assoc]
    exact unipotent_le_comap χ f T (hi.pointsEquiv T x).property)

theorem unipotentFactor_comp : unipotentFactor χ f hi hj ≫ j = i ≫ f :=
  hj.factorHom_comp _ _

include χ hi hj in
/-- Any commuting map on represented relative unipotent subgroups of affine
groups is closed when the ambient map is monic. -/
theorem isClosedSubgroup_unipotent_of_represented
    [IsAffine G.X.left] [IsAffine H.X.left] [Mono f.hom.hom]
    (g : U ⟶ V) (hg : g ≫ j = i ≫ f) : IsClosedSubgroup g := by
  let eG := AffineCoordinates.groupSchemeIso G
  let eH := AffineCoordinates.groupSchemeIso H
  let χ₀ := χ ≫ eG.inv
  let f₀ := eG.hom ≫ f ≫ eH.inv
  have hχ : χ₀ ≫ eG.hom = χ := by
    simp [χ₀, Category.assoc]
  have hψ : (χ₀ ≫ f₀) ≫ eH.hom = χ ≫ f := by
    simp [χ₀, f₀, Category.assoc]
  have hi₀ : (unipotent χ₀).IsRepresentedBy (i ≫ eG.inv) := by
    rw [unipotent_eq_comap_of_iso χ₀ eG, hχ]
    exact hi.comp_iso eG.symm
  have hj₀ : (unipotent (χ₀ ≫ f₀)).IsRepresentedBy (j ≫ eH.inv) := by
    rw [unipotent_eq_comap_of_iso (χ₀ ≫ f₀) eH, hψ]
    exact hj.comp_iso eH.symm
  have : IsIso eG.hom.hom.hom :=
    (inferInstance : IsIso ((Grp.forget _).mapIso eG).hom)
  have : IsIso eH.inv.hom.hom :=
    (inferInstance : IsIso ((Grp.forget _).mapIso eH).inv)
  have : Mono f₀.hom.hom := by
    change Mono (eG.hom.hom.hom ≫ f.hom.hom ≫ eH.inv.hom.hom)
    infer_instance
  apply Corepresented.RelativeUnipotent.isClosedSubgroup_of_represented χ₀ f₀ hi₀ hj₀ g
  simpa [f₀, Category.assoc] using congrArg (fun t => t ≫ eH.inv) hg

/-- A monic homomorphism of arbitrary affine groups induces a closed immersion
between any representatives of their relative dynamic unipotent subgroups. -/
theorem isClosedSubgroup_unipotentFactor
    [IsAffine G.X.left] [IsAffine H.X.left] [Mono f.hom.hom] :
    IsClosedSubgroup (unipotentFactor χ f hi hj) :=
  isClosedSubgroup_unipotent_of_represented χ f hi hj _ (unipotentFactor_comp χ f hi hj)

end Langlands.GroupScheme.Dynamic
