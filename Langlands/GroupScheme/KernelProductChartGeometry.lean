import Langlands.GroupScheme.KernelProductChart
import Langlands.GroupScheme.ProductProperties
import Langlands.GroupScheme.SmoothProducts
import Langlands.GroupScheme.GeometricConnectedness

/-! # Smoothness and connectedness of kernels in product charts -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

private instance smoothGeometricallyConnected_baseChange :
    ((@Smooth ⊓ @GeometricallyConnected :
      MorphismProperty Scheme.{u})).IsStableUnderBaseChange where
  of_isPullback hp hg :=
    ⟨MorphismProperty.of_isPullback (P := @Smooth) hp hg.1,
      MorphismProperty.of_isPullback (P := @GeometricallyConnected) hp hg.2⟩

private instance smoothGeometricallyConnected_comp :
    ((@Smooth ⊓ @GeometricallyConnected :
      MorphismProperty Scheme.{u})).IsStableUnderComposition where
  comp_mem f g hf hg := by
    let : Smooth f := hf.1
    let : Smooth g := hg.1
    let : GeometricallyConnected f := hf.2
    let : GeometricallyConnected g := hg.2
    exact ⟨inferInstance, GeometricallyConnected.comp f g⟩

private instance smoothGeometricallyConnected_id :
    ((@Smooth ⊓ @GeometricallyConnected :
      MorphismProperty Scheme.{u})).ContainsIdentities where
  id_mem X := by
    refine ⟨inferInstance, ⟨?_⟩⟩
    intro K _ x Y a b hp
    have : IsIso b := hp.isIso_snd_of_isIso
    exact b.homeomorph.connectedSpace_iff.mpr inferInstance

/-- Finite products preserve smoothness with geometrically connected fibres,
including the empty product. -/
theorem smooth_geometricallyConnected_pi
    {S : Scheme.{u}} {I : Type u} [Finite I] (A : I → GroupScheme S)
    (hA : ∀ i, Smooth (A i).X.hom ∧ GeometricallyConnected (A i).X.hom) :
    Smooth (pi A).X.hom ∧ GeometricallyConnected (pi A).X.hom :=
  prop_pi_hom (@Smooth ⊓ @GeometricallyConnected) A hA

/-- A finite product of smooth connected affine field groups is smooth and
connected. Ordinary connectedness is promoted using the group law. -/
theorem smooth_connected_pi_of_affine
    {k : Type u} [Field k] {I : Type u} [Finite I]
    (A : I → GroupScheme (Spec (CommRingCat.of k)))
    (hA : ∀ i, Smooth (A i).X.hom ∧ IsAffineHom (A i).X.hom ∧
      ConnectedSpace (A i).X.left) :
    Smooth (pi A).X.hom ∧ ConnectedSpace (pi A).X.left := by
  have h := smooth_geometricallyConnected_pi A (fun i => by
    let : Smooth (A i).X.hom := (hA i).1
    let : IsAffineHom (A i).X.hom := (hA i).2.1
    let : ConnectedSpace (A i).X.left := (hA i).2.2
    exact ⟨(hA i).1, (A i).geometricallyConnected_of_connected⟩)
  let : GeometricallyConnected (pi A).X.hom := h.2
  exact ⟨h.1, GeometricallyConnected.connectedSpace_of_subsingleton (f := (pi A).X.hom)⟩

namespace KernelProductChart

variable {k : Type u} [Field k] {I : Type u} [Finite I]
  {G H : GroupScheme (Spec (CommRingCat.of k))}
  {A B : I → GroupScheme (Spec (CommRingCat.of k))}
  (q : G ⟶ H) (f : ∀ i, A i ⟶ B i)
  (m : (pi A).X ⟶ G.X) (n : (pi B).X ⟶ H.X)
  (hc : m ≫ q.hom.hom = (CategoryTheory.Limits.Pi.map f).hom.hom ≫ n)
  (hn : η[(pi B).X] ≫ n = η[H.X]) [Mono n]
  (l : (kernel q).X ⟶ (pi A).X)
  (hl : l ≫ m = (kernelι q).hom.hom) [Mono m]

include hc hn hl in
/-- The product-chart comparison transfers smoothness and connectedness from
smooth connected affine factor kernels to the full ambient kernel. -/
theorem smooth_connected
    (hfactor : ∀ i, Smooth (kernel (f i)).X.hom ∧
      IsAffineHom (kernel (f i)).X.hom ∧ ConnectedSpace (kernel (f i)).X.left) :
    Smooth (kernel q).X.hom ∧ ConnectedSpace (kernel q).X.left := by
  have h := smooth_connected_pi_of_affine (fun i => kernel (f i)) hfactor
  let e := iso q f m n hc hn l hl
  exact ⟨smooth_of_over_iso e.symm h.1,
    (Scheme.homeoOfIso ((Over.forget _).mapIso e)).connectedSpace_iff.1 h.2⟩

end KernelProductChart

end Langlands.GroupScheme
