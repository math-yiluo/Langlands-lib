import Langlands.GroupScheme.SubgroupFunctor.FppfProduct
import Langlands.GroupScheme.GeometricConnectedness

/-! # Multiplication onto represented fppf products -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SubgroupFunctor

variable {S : Scheme.{u}} {G H U P : GroupScheme S}
variable {F N : SubgroupFunctor G} {i : P ⟶ G} {j : H ⟶ G} {l : U ⟶ G}

namespace IsFppfProduct

private theorem productPoint_mem (hi : IsFppfProduct F N i)
    (hH : F.IsRepresentedBy j) (hU : N.IsRepresentedBy l) :
    (fst H.X U.X ≫ j.hom.hom) * (snd H.X U.X ≫ l.hom.hom) ∈
      (range i).carrier (H.X ⊗ U.X) := by
  apply (hi.mem_range_iff _ _).mpr
  apply FppfLocallyInProduct.of_mul
  · rw [← hH.2]
    exact ⟨_, rfl⟩
  · rw [← hU.2]
    exact ⟨_, rfl⟩

/-- Multiplication of two represented factors, valued in their represented
fppf-local product. This is a scheme morphism over the base. -/
def productMul (hi : IsFppfProduct F N i)
    (hH : F.IsRepresentedBy j) (hU : N.IsRepresentedBy l) : H.X ⊗ U.X ⟶ P.X :=
  (productPoint_mem hi hH hU).choose

/-- Composing the product morphism with its inclusion is the ambient
multiplication of the two universal factor points. -/
theorem productMul_comp (hi : IsFppfProduct F N i)
    (hH : F.IsRepresentedBy j) (hU : N.IsRepresentedBy l) :
    productMul hi hH hU ≫ i.hom.hom =
      (fst H.X U.X ≫ j.hom.hom) * (snd H.X U.X ≫ l.hom.hom) :=
  (productPoint_mem hi hH hU).choose_spec

/-- A flat surjective locally finitely presented relative cover of the target
factors through the product morphism. -/
theorem exists_cover_productMul (hi : IsFppfProduct F N i)
    (hH : F.IsRepresentedBy j) (hU : N.IsRepresentedBy l) :
    ∃ (V : Over S) (v : V ⟶ P.X),
      Flat v.left ∧ Surjective v.left ∧ LocallyOfFinitePresentation v.left ∧
        ∃ r : V ⟶ H.X ⊗ U.X, r ≫ productMul hi hH hU = v := by
  have hx : i.hom.hom ∈ (range i).carrier P.X :=
    mem_range.mpr ⟨𝟙 _, Category.id_comp _⟩
  obtain ⟨V, v, hf, hs, hl, p, n, hp, hn, hv⟩ := (hi.mem_range_iff _ _).mp hx
  rw [← hH.2] at hp
  rw [← hU.2] at hn
  obtain ⟨a, rfl⟩ := mem_range.mp hp
  obtain ⟨b, rfl⟩ := mem_range.mp hn
  refine ⟨V, v, hf, hs, hl, lift a b, ?_⟩
  let : IsClosedImmersion i.hom.hom.left := hi.isClosedSubgroup
  let : Mono i.hom.hom := Over.mono_of_mono_left _
  apply (cancel_mono i.hom.hom).1
  rw [Category.assoc, productMul_comp, MonObj.comp_mul]
  simpa only [← Category.assoc, lift_fst, lift_snd] using hv.symm

/-- Multiplication onto a represented fppf-local product is an epimorphism of
schemes. -/
theorem epi_productMul (hi : IsFppfProduct F N i)
    (hH : F.IsRepresentedBy j) (hU : N.IsRepresentedBy l) :
    Epi (productMul hi hH hU).left := by
  obtain ⟨V, v, hf, hs, _, r, hr⟩ := hi.exists_cover_productMul hH hU
  let : Flat v.left := hf
  let : Surjective v.left := hs
  let : Epi v.left := Flat.epi_of_flat_of_surjective _
  have hrl : r.left ≫ (productMul hi hH hU).left = v.left :=
    congrArg (fun f => f.left) hr
  exact epi_of_epi_fac hrl

/-- Multiplication onto a represented fppf-local product is surjective on
underlying scheme points. -/
theorem surjective_productMul (hi : IsFppfProduct F N i)
    (hH : F.IsRepresentedBy j) (hU : N.IsRepresentedBy l) :
    Surjective (productMul hi hH hU).left := by
  obtain ⟨V, v, _, hs, _, r, hr⟩ := hi.exists_cover_productMul hH hU
  have hrl : r.left ≫ (productMul hi hH hU).left = v.left :=
    congrArg (fun f => f.left) hr
  have : Surjective (r.left ≫ (productMul hi hH hU).left) := hrl ▸ hs
  exact Surjective.of_comp r.left _

/-- Connectedness of the actual product descends to its represented fppf-local
image. -/
theorem connectedSpace_of_product (hi : IsFppfProduct F N i)
    (hH : F.IsRepresentedBy j) (hU : N.IsRepresentedBy l)
    [ConnectedSpace (H.X ⊗ U.X).left] : ConnectedSpace P.X.left := by
  let : Surjective (productMul hi hH hU).left := hi.surjective_productMul hH hU
  exact (productMul hi hH hU).left.surjective.connectedSpace
    (productMul hi hH hU).left.continuous

variable {k : Type u} [Field k]
variable {G H U P : GroupScheme (Spec (CommRingCat.of k))}
variable {F N : SubgroupFunctor G} {i : P ⟶ G} {j : H ⟶ G} {l : U ⟶ G}

/-- A represented fppf-local product of smooth connected affine group schemes
over a field is connected. -/
theorem connectedSpace (hi : IsFppfProduct F N i)
    (hH : F.IsRepresentedBy j) (hU : N.IsRepresentedBy l)
    [Smooth H.X.hom] [IsAffineHom H.X.hom] [ConnectedSpace H.X.left]
    [Smooth U.X.hom] [IsAffineHom U.X.hom] [ConnectedSpace U.X.left] :
    ConnectedSpace P.X.left := by
  let : GeometricallyConnected U.X.hom := U.geometricallyConnected_of_connected
  let : ConnectedSpace (H.X ⊗ U.X).left := by
    change ConnectedSpace ↥(pullback H.X.hom U.X.hom)
    infer_instance
  exact hi.connectedSpace_of_product hH hU

end IsFppfProduct

end Langlands.GroupScheme.SubgroupFunctor
