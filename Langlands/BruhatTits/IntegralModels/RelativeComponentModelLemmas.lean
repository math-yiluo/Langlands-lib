import Langlands.BruhatTits.IntegralModels.RelativeComponent
import Langlands.GroupScheme.RelativeIdentityComponent.BaseChange
import Langlands.GroupScheme.RelativeIdentityComponentProperties
import Langlands.GroupScheme.RelativeIdentityComponent.SmoothExistenceProof
import Langlands.GroupScheme.RelativeIdentityComponentDvrAffinenessProof
import Langlands.GroupScheme.IntegralModel.Iso
import Langlands.GroupScheme.IntegralModel.BaseChangeCoefficientHom

/-! # Relative identity components of smooth integral models -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace IdentityComponent

variable {k : Type u} [Field k]

/-- A homomorphism of group schemes over a field sends the identity point to the identity
point. -/
theorem map_identityPoint {A B : GroupScheme (Spec (CommRingCat.of k))} (f : A ⟶ B) :
    f.hom.hom.left (identityPoint A) = identityPoint B := by
  unfold identityPoint
  rw [← Scheme.Hom.comp_apply, ← Over.comp_left, IsMonHom.one_hom]

/-- A homomorphism of group schemes over a field maps the identity component into the
identity component. -/
theorem mapsTo_identitySet {A B : GroupScheme (Spec (CommRingCat.of k))} (f : A ⟶ B) :
    Set.MapsTo f.hom.hom.left (identitySet A) (identitySet B) := by
  intro x hx
  have himage : _root_.IsPreconnected (f.hom.hom.left '' identitySet A) :=
    (isConnected_connectedComponent.image _
      f.hom.hom.left.continuous.continuousOn).isPreconnected
  exact himage.subset_connectedComponent
    ⟨identityPoint A, mem_connectedComponent, map_identityPoint f⟩ ⟨x, hx, rfl⟩

end IdentityComponent

variable {S : Scheme.{u}}

/-- Composing with a group homomorphism preserves the relative identity-component
criterion. -/
theorem InRelativeIdentityComponent.comp {G G' : GroupScheme S} {T : Over S} {x : T ⟶ G.X}
    (hx : InRelativeIdentityComponent G x) (f : G ⟶ G') :
    InRelativeIdentityComponent G' (x ≫ f.hom.hom) := by
  intro s y hy
  rcases hy with ⟨z, rfl⟩
  change ((Over.pullback (S.fromSpecResidueField s)).map (x ≫ f.hom.hom)).left z ∈ _
  rw [Functor.map_comp, Over.comp_left, Scheme.Hom.comp_apply]
  exact IdentityComponent.mapsTo_identitySet
    ((GroupScheme.baseChange (S.fromSpecResidueField s)).map f) (hx s ⟨z, rfl⟩)

namespace IsRelativeIdentityComponent

/-- A representative of the relative identity component, composed with an isomorphism of the
ambient group scheme, represents the relative identity component of the target. -/
theorem comp_iso {G G' H : GroupScheme S} {i : H ⟶ G} (hi : IsRelativeIdentityComponent G i)
    (e : G ≅ G') : IsRelativeIdentityComponent G' (i ≫ e.hom) := by
  let : IsOpenImmersion i.hom.hom.left := hi.isOpenImmersion
  let eX : G.X ≅ G'.X := (Grp.forget (Over S)).mapIso e
  have : IsIso eX.hom.left := (Over.forget S).map_isIso eX.hom
  have hcomp : (i ≫ e.hom).hom.hom = i.hom.hom ≫ e.hom.hom.hom := Grp.comp_hom_hom _ _
  refine ⟨?_, fun T x => ?_⟩
  · rw [hcomp, Over.comp_left]
    change IsOpenImmersion (i.hom.hom.left ≫ eX.hom.left)
    infer_instance
  · constructor
    · rintro ⟨y, rfl⟩
      rw [hcomp, ← Category.assoc]
      exact ((hi.factors_iff T (y ≫ i.hom.hom)).1 ⟨y, rfl⟩).comp e.hom
    · intro hx
      have hx' : InRelativeIdentityComponent G (x ≫ e.inv.hom.hom) := hx.comp e.inv
      obtain ⟨y, hy⟩ := (hi.factors_iff T (x ≫ e.inv.hom.hom)).2 hx'
      refine ⟨y, ?_⟩
      rw [hcomp, ← Category.assoc, hy, Category.assoc, ← Grp.comp_hom_hom, e.inv_hom_id,
        Grp.id_hom_hom, Category.comp_id]

end IsRelativeIdentityComponent

/-- Over a field, a group scheme with connected underlying space is its own relative identity
component. -/
theorem isRelativeIdentityComponent_id_of_connectedSpace {k : Type u} [Field k]
    (G : GroupScheme (Spec (CommRingCat.of k))) [ConnectedSpace G.X.left] :
    IsRelativeIdentityComponent G (𝟙 G) := by
  refine ⟨?_, fun T x => ⟨fun _ => ?_, fun _ => ⟨x, ?_⟩⟩⟩
  · change IsOpenImmersion (𝟙 G.X.left)
    infer_instance
  · intro s y _
    have hconn : ConnectedSpace (G.X.hom.fiber s) := by
      let e := G.X.hom.fiberHomeo s
      have hs (z : G.X.left) : z ∈ G.X.hom ⁻¹' {s} := Subsingleton.elim _ _
      refine Function.Surjective.connectedSpace (f := fun z => e.symm ⟨z, hs z⟩) ?_ ?_
      · intro w
        refine ⟨(e w).1, ?_⟩
        simp
      · exact e.symm.continuous.comp (continuous_id.subtype_mk hs)
    have : ConnectedSpace (RelativeIdentityComponent.residueFiber G s).X.left := hconn
    change y ∈ connectedComponent _
    rw [PreconnectedSpace.connectedComponent_eq_univ]
    trivial
  · rw [Grp.id_hom_hom, Category.comp_id]

end Langlands.GroupScheme

namespace Langlands.BruhatTits.IntegralModels

open GroupScheme

namespace RelativeComponentModelData

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]
  {G : GroupScheme (Spec (CommRingCat.of K))}

/-- A smooth integral model over a discrete valuation ring, of a group whose underlying space is
connected, is the full model of a relative-component datum: its relative identity component,
with the generic identification induced from the full model, is the neutral model. -/
theorem exists_full_eq [IsDiscreteValuationRing R] [ConnectedSpace G.X.left]
    (M : IntegralModel R K G) (hM : M.IsSmooth) :
    ∃ D : RelativeComponentModelData R K G, D.full = M := by
  obtain ⟨H, i, hi, hHs, hHc⟩ := RelativeIdentityComponent.smoothExistence _ M.group hM
  let : GeometricallyConnected H.X.hom := hHc
  let : Smooth H.X.hom := hHs
  let : IsAffineHom H.X.hom := RelativeIdentityComponent.smoothDvrAffineness R M.group hM inferInstance H i hi
  have hiK := (hi.baseChange (Spec.algebraMap R K)).comp_iso M.genericIso
  have hid := isRelativeIdentityComponent_id_of_connectedSpace G
  let N : IntegralModel R K G := { group := H, genericIso := hiK.iso hid }
  exact ⟨⟨M, N, hM, hHs, fun x => inferInstance, ⟨i, (hiK.iso_hom_comp hid).symm⟩, hi⟩, rfl⟩

end RelativeComponentModelData

end Langlands.BruhatTits.IntegralModels
