import Langlands.GroupScheme.Reductive.TitsComponentFactorStatement

/-! # Cartan component transport and its full stabilizer action -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme
namespace TitsIndexData

variable {k : Type u} [Field k]
  {G H : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  [IsAffineHom H.X.hom] [LocallyOfFiniteType H.X.hom]
  (d : TitsIndexData G)

/-- Transport connectivity along an injective map preserving all ordered Cartan entries. -/
theorem CartanConnected.map {e : TitsIndexData H} {f : d.Vertex → e.Vertex}
    (hf : Function.Injective f) (hc : ∀ a b, e.cartan (f a) (f b) = d.cartan a b)
    {a b : d.Vertex} (h : d.CartanConnected a b) : e.CartanConnected (f a) (f b) := by
  induction h with
  | rel a b hab =>
    exact Relation.EqvGen.rel _ _ ⟨fun h => hab.1 (hf h), by rw [hc]; exact hab.2⟩
  | refl a => exact e.cartanConnected_refl (f a)
  | symm a b _ ih => exact ih.symm
  | trans a b c _ _ ih₁ ih₂ => exact ih₁.trans e ih₂

/-- The full star action preserves connectivity in the actual Cartan diagram. -/
theorem CartanConnected.star {a b : d.Vertex} (h : d.CartanConnected a b)
    (σ : SeparableClosure k ≃ₐ[k] SeparableClosure k) :
    d.CartanConnected (d.star σ a) (d.star σ b) := by
  apply h.map d (e := d) (f := d.star σ) ?_
    (fun _ _ => (d.pinning.starAction σ).val.toHom.pairing)
  intro x y hxy
  have h := congrArg (d.star σ⁻¹) hxy
  simpa only [← d.star_mul, inv_mul_cancel, d.star_one] using h

/-- Applying one Galois element to both endpoints does not change connectivity. -/
theorem cartanConnected_star_iff (σ : SeparableClosure k ≃ₐ[k] SeparableClosure k)
    (a b : d.Vertex) :
    d.CartanConnected (d.star σ a) (d.star σ b) ↔ d.CartanConnected a b := by
  constructor
  · intro h
    have h' := h.star d σ⁻¹
    simpa only [← d.star_mul, inv_mul_cancel, d.star_one] using h'
  · exact fun h => h.star d σ

/-- The subgroup that stabilizes the entire component of the chosen vertex. -/
def cartanComponentStabilizer (a : d.Vertex) :
    Subgroup (SeparableClosure k ≃ₐ[k] SeparableClosure k) where
  carrier := {σ | d.CartanConnected a (d.star σ a)}
  one_mem' := by
    change d.CartanConnected a (d.star 1 a)
    simpa only [d.star_one] using d.cartanConnected_refl a
  mul_mem' := by
    intro σ τ hσ hτ
    change d.CartanConnected a (d.star (σ * τ) a)
    simpa only [d.star_mul] using hσ.trans d (hτ.star d σ)
  inv_mem' := by
    intro σ hσ
    have h := (hσ.star d σ⁻¹).symm
    change d.CartanConnected a (d.star σ⁻¹ a)
    simpa only [← d.star_mul, inv_mul_cancel, d.star_one] using h

@[simp] theorem mem_cartanComponentStabilizer (a : d.Vertex)
    (σ : SeparableClosure k ≃ₐ[k] SeparableClosure k) :
    σ ∈ d.cartanComponentStabilizer a ↔ d.CartanConnected a (d.star σ a) := Iff.rfl

/-- One stabilizer element acts on all vertices of the component at once. -/
def cartanComponentStarPerm (a : d.Vertex) (σ : d.cartanComponentStabilizer a) :
    Equiv.Perm (d.CartanComponent a) where
  toFun b := ⟨d.star σ.val b.val,
    ((d.mem_cartanComponentStabilizer a σ.val).mp σ.property).trans d
      (b.property.star d σ.val)⟩
  invFun b := ⟨d.star σ.val⁻¹ b.val,
    ((d.mem_cartanComponentStabilizer a σ.val⁻¹).mp
      ((d.cartanComponentStabilizer a).inv_mem σ.property)).trans d
        (b.property.star d σ.val⁻¹)⟩
  left_inv b := by
    apply Subtype.ext
    change d.star σ.val⁻¹ (d.star σ.val b.val) = b.val
    rw [← d.star_mul, inv_mul_cancel, d.star_one]
  right_inv b := by
    apply Subtype.ext
    change d.star σ.val (d.star σ.val⁻¹ b.val) = b.val
    rw [← d.star_mul, mul_inv_cancel, d.star_one]

@[simp] theorem cartanComponentStarPerm_apply_val (a : d.Vertex)
    (σ : d.cartanComponentStabilizer a) (b : d.CartanComponent a) :
    (d.cartanComponentStarPerm a σ b).val = d.star σ.val b.val := rfl

/-- The full stabilizer permutation representation on an actual Cartan component. -/
def cartanComponentStarRepresentation (a : d.Vertex) :
    d.cartanComponentStabilizer a →* Equiv.Perm (d.CartanComponent a) where
  toFun := d.cartanComponentStarPerm a
  map_one' := by
    apply Equiv.ext
    intro b
    apply Subtype.ext
    exact d.star_one b.val
  map_mul' σ τ := by
    apply Equiv.ext
    intro b
    apply Subtype.ext
    exact d.star_mul σ.val τ.val b.val

/-- The stabilizer acts by automorphisms of every ordered Cartan entry. -/
theorem cartan_componentStarPerm (a : d.Vertex) (σ : d.cartanComponentStabilizer a)
    (b c : d.CartanComponent a) :
    d.cartan (d.cartanComponentStarPerm a σ b).val
      (d.cartanComponentStarPerm a σ c).val = d.cartan b.val c.val :=
  (d.pinning.starAction σ.val).val.toHom.pairing

end TitsIndexData

namespace TitsIndexEquiv

variable {k : Type u} [Field k]
  {G H : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  [IsAffineHom H.X.hom] [LocallyOfFiniteType H.X.hom]
  {d : TitsIndexData G} {e : TitsIndexData H} (h : TitsIndexEquiv d e)

/-- Equivalence of actual indices preserves and reflects their Cartan components. -/
theorem cartanConnected_iff (a b : d.Vertex) :
    e.CartanConnected (h.vertices a) (h.vertices b) ↔ d.CartanConnected a b := by
  constructor
  · intro hab
    have hc : ∀ x y, d.cartan (h.vertices.symm x) (h.vertices.symm y) = e.cartan x y := by
      intro x y
      simpa only [Equiv.apply_symm_apply] using
        (h.cartan_eq (h.vertices.symm x) (h.vertices.symm y)).symm
    have h' := hab.map e h.vertices.symm.injective hc
    simpa only [Equiv.symm_apply_apply] using h'
  · exact fun hab => hab.map d h.vertices.injective h.cartan_eq

/-- Restrict an index equivalence to the whole connected Cartan component. -/
def cartanComponentEquiv (a : d.Vertex) :
    d.CartanComponent a ≃ e.CartanComponent (h.vertices a) :=
  h.vertices.subtypeEquiv (fun b => (h.cartanConnected_iff a b).symm)

@[simp] theorem cartanComponentEquiv_apply_val (a : d.Vertex) (b : d.CartanComponent a) :
    (h.cartanComponentEquiv a b).val = h.vertices b.val := rfl

/-- The component equivalence intertwines each stabilizing Galois element. -/
theorem cartanComponentStarPerm_eq (a : d.Vertex)
    (σ : d.cartanComponentStabilizer a) (b : d.CartanComponent a) :
    (h.cartanComponentEquiv a (d.cartanComponentStarPerm a σ b)).val =
      e.star σ.val (h.cartanComponentEquiv a b).val := h.star_eq σ.val b.val

/-- Equivalent indices have precisely the same component stabilizer subgroup. -/
theorem cartanComponentStabilizer_eq (a : d.Vertex) :
    d.cartanComponentStabilizer a = e.cartanComponentStabilizer (h.vertices a) := by
  apply Subgroup.ext
  intro σ
  change d.CartanConnected a (d.star σ a) ↔
    e.CartanConnected (h.vertices a) (e.star σ (h.vertices a))
  rw [← h.star_eq]
  exact (h.cartanConnected_iff a (d.star σ a)).symm

end TitsIndexEquiv

namespace TitsIndexEquiv

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {d e : TitsIndexData G} (h : TitsIndexEquiv d e)

/-- Change the actual index of a component factor of the same group, retaining
the entire group witness and the two simultaneous full-star lifts. -/
def componentFactor {a : d.Vertex} (F : d.ComponentFactor a) :
    e.ComponentFactor (h.vertices a) where
  extension := F.extension
  factor := F.factor
  simplyConnected := F.simplyConnected
  absolutelyAlmostSimple := F.absolutelyAlmostSimple
  complement := F.complement
  complement_simplyConnected := F.complement_simplyConnected
  cover := F.cover
  cover_simplyConnected := F.cover_simplyConnected
  cover_centralIsogeny := F.cover_centralIsogeny
  index := F.index
  vertexEquiv := F.vertexEquiv.trans (h.cartanComponentEquiv a)
  cartan_eq b c :=
    (h.cartan_eq (F.vertexEquiv b).val (F.vertexEquiv c).val).trans (F.cartan_eq b c)
  stabilizer_lift σ hσ := by
    have hd : d.CartanConnected a (d.star σ a) := by
      apply (h.cartanConnected_iff a (d.star σ a)).mp
      rw [h.star_eq]
      exact hσ
    obtain ⟨τ, hτ⟩ := F.stabilizer_lift σ hd
    refine ⟨τ, fun b => ?_⟩
    change h.vertices (F.vertexEquiv (F.index.star τ b)).val =
      e.star σ (h.vertices (F.vertexEquiv b).val)
    rw [hτ b, h.star_eq]
  star_lift τ := by
    obtain ⟨σ, hσ⟩ := F.star_lift τ
    refine ⟨σ, fun b => ?_⟩
    change h.vertices (F.vertexEquiv (F.index.star τ b)).val =
      e.star σ (h.vertices (F.vertexEquiv b).val)
    rw [hσ b, h.star_eq]
  anisotropic := F.anisotropic

end TitsIndexEquiv

end Langlands.GroupScheme
