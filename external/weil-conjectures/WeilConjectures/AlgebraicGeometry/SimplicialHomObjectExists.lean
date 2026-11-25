/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SemiRepresentableObject
public import Mathlib.AlgebraicTopology.SimplicialSet.Finite
import WeilConjectures.AlgebraicTopology.SimplicialIndexFiniteInitial

/-!
# Objects of compatible simplicial maps in semi-representable objects

Source: Stacks Project, Tags 017J and 017K, applied to the category of formal étale
families using Tag 01G2 (auxiliary; not a blueprint node).
-/

@[expose] public section

universe u w t

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

namespace AlgebraicGeometry.Scheme

/-- The compatible families indexed by a finite simplicial set are represented by a
semi-representable object. Source: Stacks Project, Tags 017J, 017K and 01G2
(auxiliary; not a blueprint node).

Proof:
1. Form the category of simplices `(n, s)` of `S`, with arrows `(m, t) → (n, s)`
   given by monotone maps `φ : [m] → [n]` satisfying `S(φ)(s) = t`. Its opposite
   carries the diagram with value `K_n` and arrow `K(φ)`. By
   def-weil-pbc-simplicial-set and def-weil-pbc-semi-representable-object, cones
   with vertex `W` are exactly the compatible families in the statement (017J).
2. Finitely many nondegenerate simplices give a degree bound `m₀`. By
   lem-weil-pbc-simplicial-index-finite-initial, the opposite of the full subcategory
   of degrees at most `2 m₀` is finite and initial. The same node's limit-comparison
   clause (002R) reduces the full diagram's limit to this finite restriction (017K).
3. By lem-weil-pbc-semi-representable-finite-limits, applied to the small étale
   site as in def-weil-pbc-semi-representable-object, that finite limit exists (01G2).
   Let `H` be its vertex. Initiality extends its universal cone to all degrees,
   yielding the maps `u_s` and their compatibility equations. The cone correspondence
   in step 1 and the limit's universal property give the unique map `g` for every
   compatible family `f_s`, with `g ≫ u_s = f_s`. -/
theorem exists_simplicial_hom_object (X : Scheme.{u})
    (K : SimplicialObject (FormalCoproduct.{w} X.Etale)) (S : SSet.{t})
    [S.Finite] (hfinite : ∀ n : ℕ, Finite (S.obj (op ⦋n⦌)))
    (hnonempty : ∀ n : ℕ, Nonempty (S.obj (op ⦋n⦌))) :
    ∃ (H : FormalCoproduct.{w} X.Etale)
      (u : ∀ (n : ℕ), S.obj (op ⦋n⦌) → (H ⟶ K.obj (op ⦋n⦌))),
      (∀ (m n : ℕ) (φ : ⦋m⦌ ⟶ ⦋n⦌) (s : S.obj (op ⦋n⦌)),
        u n s ≫ K.map φ.op = u m (S.map φ.op s)) ∧
      (∀ (W : FormalCoproduct.{w} X.Etale)
        (f : ∀ (n : ℕ), S.obj (op ⦋n⦌) → (W ⟶ K.obj (op ⦋n⦌))),
        (∀ (m n : ℕ) (φ : ⦋m⦌ ⟶ ⦋n⦌) (s : S.obj (op ⦋n⦌)),
          f n s ≫ K.map φ.op = f m (S.map φ.op s)) →
        ∃! g : W ⟶ H, ∀ (n : ℕ) (s : S.obj (op ⦋n⦌)), g ≫ u n s = f n s) := by
  classical
  obtain ⟨d, hd⟩ := S.hasDimensionLT_of_finite
  let : S.HasDimensionLT d := hd
  have hdegenerate : ∀ n : ℕ, d < n → ∀ s : S.obj (op ⦋n⦌),
      s ∈ S.degenerate n := by
    intro n hn s
    rw [S.degenerate_eq_univ_of_hasDimensionLT d n (Nat.le_of_lt hn)]
    trivial
  obtain ⟨hobj, hhom, _, _, _, hlimit, _⟩ :=
    S.simplicialIndex_finite_initial hfinite hnonempty d hdegenerate
  let T := ObjectProperty.FullSubcategory
    (fun x : S.Elements ↦ x.obj.unop.len ≤ 2 * d)
  let D := Functor.Elements.π S ⋙ K
  let : Finite T := hobj
  let (a b : T) : Finite (a ⟶ b) := hhom a b
  -- Raise the hom universe to obtain a small finite category equivalent to T.
  let : Finite (AsSmall.{0} T) := Finite.of_equiv T Equiv.ulift.symm
  let : Fintype (AsSmall.{0} T) := Fintype.ofFinite _
  let : FinCategory (AsSmall.{0} T) :=
    { fintypeHom := fun a b ↦ by
        change Fintype (ULift.{t} ((AsSmall.down.obj a : T) ⟶ (AsSmall.down.obj b : T)))
        let : Fintype ((AsSmall.down.obj a : T) ⟶ (AsSmall.down.obj b : T)) := Fintype.ofFinite _
        infer_instance }
  let : HasLimitsOfShape T (FormalCoproduct.{w} X.Etale) :=
    hasLimitsOfShape_of_equivalence (AsSmall.equiv : T ≌ AsSmall.{0} T).symm
  let : HasLimit D := (hlimit _ D).mpr inferInstance
  refine ⟨limit D, fun n s ↦ limit.π D (S.elementsMk (op ⦋n⦌) s), ?_, ?_⟩
  · intro m n φ s
    exact limit.w D (Functor.Elements.homMk
      (x := S.elementsMk (op ⦋n⦌) s) (y := S.elementsMk (op ⦋m⦌) (S.map φ.op s)) φ.op rfl)
  · intro W f hf
    let c : Cone D :=
      { pt := W
        π :=
          { app := fun a ↦ f a.obj.unop.len a.val
            naturality := by
              intro a b g
              dsimp [D]
              simpa only [Category.id_comp, Quiver.Hom.op_unop, g.map_val,
                Functor.Elements.π_obj, Functor.Elements.π_map] using
                (hf b.obj.unop.len a.obj.unop.len g.hom.unop a.val).symm } }
    refine ⟨limit.lift D c, ?_, ?_⟩
    · intro n s
      exact limit.lift_π c (S.elementsMk (op ⦋n⦌) s)
    · intro g hg
      apply limit.hom_ext
      intro a
      exact (hg a.obj.unop.len a.val).trans (limit.lift_π c a).symm

end AlgebraicGeometry.Scheme
