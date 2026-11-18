import Langlands.GroupScheme.Reductive.TitsCartanComponentField
import Langlands.GroupScheme.Reductive.TitsIndexSeparableScalarExtension

/-! # Actual Cartan components over their finite stabilizer fields -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.TitsIndexData

section AcrossFields

variable {k k' : Type u} [Field k] [Field k']
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {H : GroupScheme (Spec (CommRingCat.of k'))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  [IsAffineHom H.X.hom] [LocallyOfFiniteType H.X.hom]
  (d : TitsIndexData G)

/-- Cartan connectivity transports through pairing-preserving injective maps,
also when the actual groups have different ground fields. -/
theorem CartanConnected.mapAcrossFields {e : TitsIndexData H} {f : d.Vertex → e.Vertex}
    (hf : Function.Injective f) (hc : ∀ a b, e.cartan (f a) (f b) = d.cartan a b)
    {a b : d.Vertex} (h : d.CartanConnected a b) : e.CartanConnected (f a) (f b) := by
  induction h with
  | rel a b hab =>
    exact Relation.EqvGen.rel _ _ ⟨fun h => hab.1 (hf h), by rw [hc]; exact hab.2⟩
  | refl a => exact e.cartanConnected_refl (f a)
  | symm a b _ ih => exact ih.symm
  | trans a b c _ _ ih₁ ih₂ => exact ih₁.trans e ih₂

end AcrossFields

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {d : TitsIndexData G} {E : IntermediateField k (SeparableClosure k)}

local instance componentScalarClosureAlgebra : Algebra E (SeparableClosure E) :=
  (separableClosure E (AlgebraicClosure E)).algebra

local instance componentScalarAffine :
    IsAffineHom ((GroupScheme.baseChange (algebraBaseMap k E)).obj G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom _)
  infer_instance

local instance componentScalarFiniteType :
    LocallyOfFiniteType ((GroupScheme.baseChange (algebraBaseMap k E)).obj G).X.hom := by
  change LocallyOfFiniteType (CategoryTheory.Limits.pullback.snd G.X.hom _)
  infer_instance

namespace SeparableScalarExtension

variable {e : SeparableClosure E ≃ₐ[E] SeparableClosure k}
  (F : d.SeparableScalarExtension E e)

/-- The actual scalar-extension comparison preserves and reflects connectivity. -/
theorem cartanConnected_iff (a b : d.Vertex) :
    F.index.CartanConnected (F.vertices a) (F.vertices b) ↔ d.CartanConnected a b := by
  constructor
  · intro h
    have hc : ∀ x y, d.cartan (F.vertices.symm x) (F.vertices.symm y) = F.index.cartan x y := by
      intro x y
      simpa only [Equiv.apply_symm_apply] using
        (F.cartan_eq (F.vertices.symm x) (F.vertices.symm y)).symm
    have h' := h.mapAcrossFields F.index F.vertices.symm.injective hc
    simpa only [Equiv.symm_apply_apply] using h'
  · exact fun h => h.mapAcrossFields d F.vertices.injective F.cartan_eq

/-- Restrict actual scalar-extension vertices to the entire chosen Cartan component. -/
def cartanComponentEquiv (a : d.Vertex) :
    d.CartanComponent a ≃ F.index.CartanComponent (F.vertices a) :=
  F.vertices.subtypeEquiv (fun b => (F.cartanConnected_iff a b).symm)

@[simp] theorem cartanComponentEquiv_apply_val (a : d.Vertex) (b : d.CartanComponent a) :
    (F.cartanComponentEquiv a b).val = F.vertices b.val := rfl

end SeparableScalarExtension

variable (d)

/-- An actual index of the base-changed group over the finite component field,
compared to every original vertex and full star element. -/
def componentFieldIndexComparison (a : d.Vertex) :
    d.SeparableScalarExtension (d.cartanComponentField a)
      (d.cartanComponentSeparableClosureEquiv a) :=
  d.separableScalarExtension (d.cartanComponentField a) (d.cartanComponentSeparableClosureEquiv a)

/-- The original component and the corresponding actual component over its
finite separable stabilizer field have equivalent full vertex sets. -/
def componentFieldCartanEquiv (a : d.Vertex) :
    d.CartanComponent a ≃ (d.componentFieldIndexComparison a).index.CartanComponent
      ((d.componentFieldIndexComparison a).vertices a) :=
  (d.componentFieldIndexComparison a).cartanComponentEquiv a

/-- Over the component field every absolute Galois element stabilizes the
corresponding component of the actual base-changed Tits index. -/
theorem componentFieldIndexComparison_component_stable (a : d.Vertex)
    (τ : SeparableClosure (d.cartanComponentField a) ≃ₐ[d.cartanComponentField a]
      SeparableClosure (d.cartanComponentField a)) :
    (d.componentFieldIndexComparison a).index.CartanConnected
      ((d.componentFieldIndexComparison a).vertices a)
      ((d.componentFieldIndexComparison a).index.star τ
        ((d.componentFieldIndexComparison a).vertices a)) := by
  let F := d.componentFieldIndexComparison a
  let σ := d.cartanComponentAbsoluteGaloisEquiv a τ
  have hσ : d.CartanConnected a (d.star σ.val a) :=
    (d.mem_cartanComponentStabilizer a σ.val).mp σ.property
  have h := (F.cartanConnected_iff a (d.star σ.val a)).mpr hσ
  have hs : F.vertices (d.star σ.val a) = F.index.star τ (F.vertices a) := F.star_eq τ a
  exact hs ▸ h

/-- One relative absolute Galois element lifts each stabilizing original
Galois element, simultaneously on all simple vertices. -/
theorem componentFieldIndexComparison_stabilizer_lift (a : d.Vertex)
    (σ : SeparableClosure k ≃ₐ[k] SeparableClosure k)
    (hσ : d.CartanConnected a (d.star σ a)) :
    ∃ τ : SeparableClosure (d.cartanComponentField a) ≃ₐ[d.cartanComponentField a]
      SeparableClosure (d.cartanComponentField a),
      ∀ b : d.Vertex,
        (d.componentFieldIndexComparison a).vertices (d.star σ b) =
          (d.componentFieldIndexComparison a).index.star τ
            ((d.componentFieldIndexComparison a).vertices b) := by
  let s : d.cartanComponentStabilizer a :=
    ⟨σ, (d.mem_cartanComponentStabilizer a σ).mpr hσ⟩
  let τ := (d.cartanComponentAbsoluteGaloisEquiv a).symm s
  have hτ : (d.cartanComponentAbsoluteGaloisEquiv a τ).val = σ :=
    congrArg Subtype.val ((d.cartanComponentAbsoluteGaloisEquiv a).apply_symm_apply s)
  refine ⟨τ, fun b => ?_⟩
  have hs : (d.componentFieldIndexComparison a).vertices
      (d.star (d.cartanComponentAbsoluteGaloisEquiv a τ).val b) =
      (d.componentFieldIndexComparison a).index.star τ
        ((d.componentFieldIndexComparison a).vertices b) :=
    (d.componentFieldIndexComparison a).star_eq τ b
  exact hτ ▸ hs

/-- Every absolute Galois element of the component field has a single original
stabilizer lift, simultaneously on all simple vertices. -/
theorem componentFieldIndexComparison_star_lift (a : d.Vertex)
    (τ : SeparableClosure (d.cartanComponentField a) ≃ₐ[d.cartanComponentField a]
      SeparableClosure (d.cartanComponentField a)) :
    ∃ σ : SeparableClosure k ≃ₐ[k] SeparableClosure k,
      d.CartanConnected a (d.star σ a) ∧
      ∀ b : d.Vertex,
        (d.componentFieldIndexComparison a).vertices (d.star σ b) =
          (d.componentFieldIndexComparison a).index.star τ
            ((d.componentFieldIndexComparison a).vertices b) := by
  refine ⟨(d.cartanComponentAbsoluteGaloisEquiv a τ).val, ?_,
    fun b => (d.componentFieldIndexComparison a).star_eq τ b⟩
  exact (d.mem_cartanComponentStabilizer a _).mp
    (d.cartanComponentAbsoluteGaloisEquiv a τ).property

end Langlands.GroupScheme.TitsIndexData
