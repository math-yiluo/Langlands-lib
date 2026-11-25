/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.SimplicialOrdinalPath
import WeilConjectures.CategoryTheory.OrdinalPathFaceIntersection
public import WeilConjectures.AlgebraicTopology.SimplexFaceFamilyGluing
public import WeilConjectures.CategoryTheory.ProperFaceMatchingObject
import Mathlib.Tactic

/-!
# The finite boundary family for the ordered path construction

Source: Stacks, Tags 017J and 01GN, the endpoint-and-boundary gluing argument.
(auxiliary; not a blueprint node)
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open SimplexCategory.OrdinalPath

namespace CategoryTheory.SimplicialObject.OrdinalBoundary

abbrev Generator (n : ℕ) := Bool ⊕ ProperFaceCategory n

def degree (n : ℕ) : Generator n → ℕ
  | .inl _ => n
  | .inr a => 2 * a.obj.left.len + 1

def face (n : ℕ) : ∀ i : Generator n, ⦋degree n i⦌ ⟶ ⦋2 * n + 1⦌
  | .inl false => left ⦋n⦌
  | .inl true => right ⦋n⦌
  | .inr a => map a.obj.hom

/-- The two endpoint simplices together with the doubled proper faces. -/
def subcomplex (n : ℕ) : (Δ[2 * n + 1] : SSet.{w}).Subcomplex :=
  faceUnion (degree n) (face n)

/-- Every degree contains a constant simplex from the first endpoint. -/
theorem subcomplex_nonempty (n m : ℕ) :
    Nonempty ((subcomplex.{w} n).toSSet.obj (op ⦋m⦌)) := by
  let q : ⦋m⦌ ⟶ ⦋n⦌ := SimplexCategory.Hom.mk ⟨fun _ ↦ 0, fun _ _ _ ↦ le_rfl⟩
  refine ⟨⟨SSet.stdSimplex.objEquiv.symm (q ≫ left ⦋n⦌), ?_⟩⟩
  rw [subcomplex, mem_faceUnion_iff]
  exact ⟨.inl false, q, rfl⟩

/-- Compatible lower doubled simplices and full endpoint simplices glue on their union.
Source: Stacks, Tags 017J and 01GN. Equal endpoint faces agree by monicity; opposite
endpoints are disjoint. The intersection of an endpoint with a doubled face is the
corresponding endpoint of that face, where the supplied endpoint equations give
agreement. Two doubled faces intersect in the double of their nonempty common face;
the lower matching family's naturality gives agreement there. Apply face-family
gluing to these pairwise agreements.
(auxiliary; not a blueprint node) -/
theorem exists_family {C : Type u} [Category.{v} C] (V : SimplicialObject C)
    (n : ℕ) (T : C) (l r : T ⟶ V.obj (op ⦋n⦌))
    (p : (Functor.const _).obj T ⟶ (ordinalPath V).properFaceDiagram n)
    (hl : ∀ a : ProperFaceCategory n,
      p.app (op a) ≫ V.map (left a.obj.left).op = l ≫ V.map a.obj.hom.op)
    (hr : ∀ a : ProperFaceCategory n,
      p.app (op a) ≫ V.map (right a.obj.left).op = r ≫ V.map a.obj.hom.op) :
    ∃ f : ∀ m : ℕ, (subcomplex.{w} n).toSSet.obj (op ⦋m⦌) →
        (T ⟶ V.obj (op ⦋m⦌)),
      (∀ (m k : ℕ) (φ : ⦋m⦌ ⟶ ⦋k⦌)
        (s : (subcomplex.{w} n).toSSet.obj (op ⦋k⦌)),
        f k s ≫ V.map φ.op = f m ((subcomplex n).toSSet.map φ.op s)) ∧
      (∀ i, f (degree n i) ⟨SSet.stdSimplex.objEquiv.symm (face n i),
        faceUnion_generator_mem (degree n) (face n) i⟩ =
        (match i with | .inl false => l | .inl true => r | .inr a => p.app (op a))) := by
  let val : ∀ i : Generator n, T ⟶ V.obj (op ⦋degree n i⦌)
    | .inl false => l
    | .inl true => r
    | .inr a => p.app (op a)
  apply glue_face_family V T (degree n) (face n) val
  have hleft (a : ProperFaceCategory n) (m : ℕ) (q : ⦋m⦌ ⟶ ⦋n⦌)
      (t : ⦋m⦌ ⟶ obj a.obj.left) (h : q ≫ left ⦋n⦌ = t ≫ map a.obj.hom) :
      l ≫ V.map q.op = p.app (op a) ≫ V.map t.op := by
    obtain ⟨s, hq, ht⟩ := left_face_factor a.obj.hom q t h
    rw [hq, ht, op_comp, op_comp, V.map_comp, V.map_comp,
      ← Category.assoc, ← Category.assoc, hl]
  have hright (a : ProperFaceCategory n) (m : ℕ) (q : ⦋m⦌ ⟶ ⦋n⦌)
      (t : ⦋m⦌ ⟶ obj a.obj.left) (h : q ≫ right ⦋n⦌ = t ≫ map a.obj.hom) :
      r ≫ V.map q.op = p.app (op a) ≫ V.map t.op := by
    obtain ⟨s, hq, ht⟩ := right_face_factor a.obj.hom q t h
    rw [hq, ht, op_comp, op_comp, V.map_comp, V.map_comp,
      ← Category.assoc, ← Category.assoc, hr]
  intro i j m q t h
  rcases i with bi | ai
  · rcases j with bj | aj
    · cases bi <;> cases bj
      · have he : q = t := (cancel_mono (left ⦋n⦌)).mp h
        exact congrArg (fun z ↦ l ≫ V.map z.op) he
      · have he := congrArg (fun z : ⦋m⦌ ⟶ obj ⦋n⦌ ↦ z.toOrderHom 0) h
        exact False.elim (left_right_ne _ _ he)
      · have he := congrArg (fun z : ⦋m⦌ ⟶ obj ⦋n⦌ ↦ z.toOrderHom 0) h
        exact False.elim (left_right_ne _ _ he.symm)
      · have he : q = t := (cancel_mono (right ⦋n⦌)).mp h
        exact congrArg (fun z ↦ r ≫ V.map z.op) he
    · cases bi
      · exact hleft aj m q t h
      · exact hright aj m q t h
  · rcases j with bj | aj
    · cases bj
      · exact (hleft ai m t q h.symm).symm
      · exact (hright ai m t q h.symm).symm
    · let a := ai
      let b := aj
      let _ : Mono a.obj.hom := SimplexCategory.mono_iff_injective.mpr a.property.2
      let _ : Mono b.obj.hom := SimplexCategory.mono_iff_injective.mpr b.property.2
      obtain ⟨k, s, t', z, hs, ht, hst, hq, ht'⟩ :=
        doubled_face_intersection a.obj.hom b.obj.hom q t h
      let := hs
      let := ht
      let c : ProperFaceCategory n :=
        ⟨Over.mk (s ≫ a.obj.hom),
          lt_of_le_of_lt (SimplexCategory.len_le_of_mono s) a.property.1,
          (by
            change Function.Injective (s ≫ a.obj.hom).toOrderHom
            exact SimplexCategory.mono_iff_injective.mp inferInstance)⟩
      let ga : c ⟶ a := ObjectProperty.homMk (Over.homMk s rfl)
      let gb : c ⟶ b := ObjectProperty.homMk (Over.homMk t' hst.symm)
      have ha := p.naturality ga.op
      have hb := p.naturality gb.op
      change 𝟙 T ≫ p.app (op c) = p.app (op a) ≫ V.map (map s).op at ha
      change 𝟙 T ≫ p.app (op c) = p.app (op b) ≫ V.map (map t').op at hb
      rw [Category.id_comp] at ha hb
      change p.app (op a) ≫ V.map q.op = p.app (op b) ≫ V.map t.op
      rw [← hq, ← ht', op_comp, op_comp, V.map_comp, V.map_comp,
        ← Category.assoc, ← Category.assoc, ← ha, ← hb]

end CategoryTheory.SimplicialObject.OrdinalBoundary
