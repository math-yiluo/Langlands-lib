/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.EtaleHypercover
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.AlgebraicGeometry.EtaleSimplicialMatching
import WeilConjectures.AlgebraicGeometry.SimplicialHomStandardSimplex
import WeilConjectures.AlgebraicGeometry.HypercoverFiniteSimplexLifting

/-!
# Local extension of ordinary étale simplex families

Source: Stacks, Tag 01GN. Apply finite-simplex lifting after the fully faithful
singleton inclusion, and unpack the representing universal families.
(auxiliary; not a blueprint node)
-/

@[expose] public section

universe u t

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

namespace AlgebraicGeometry.EtaleSimplicialMatching

/-- A family on a finite nonempty subcomplex of a standard simplex extends locally.
Source: Stacks, Tag 01GN. The singleton inclusion is fully faithful; its compatible
families are represented by the Hom objects in Tags 017J and 017K. Apply finite-simplex
lifting to the representing point of the given family, then evaluate its restriction
identity at each simplex and use full faithfulness to return to the étale category.
(auxiliary; not a blueprint node) -/
theorem locally_extend_simplex {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (V : SimplicialObject X.Etale) (hV : IsEtaleHypercover V) (n : ℕ)
    (A : (Δ[n] : SSet.{t}).Subcomplex) [A.toSSet.Finite]
    (hAnonempty : ∀ m : ℕ, Nonempty (A.toSSet.obj (op ⦋m⦌))) (T : X.Etale)
    (f : ∀ m : ℕ, A.toSSet.obj (op ⦋m⦌) → (T ⟶ V.obj (op ⦋m⦌)))
    (hf : ∀ (m k : ℕ) (φ : ⦋m⦌ ⟶ ⦋k⦌) (s : A.toSSet.obj (op ⦋k⦌)),
      f k s ≫ V.map φ.op = f m (A.toSSet.map φ.op s)) :
    ∃ (ι : Type u) (Tc : ι → X.Etale) (p : ∀ c : ι, Tc c ⟶ T),
      Sieve.ofArrows Tc p ∈ X.smallEtaleTopology T ∧
        ∃ g : ∀ c : ι, Tc c ⟶ V.obj (op ⦋n⦌),
          ∀ (c : ι) (m : ℕ) (s : A.toSSet.obj (op ⦋m⦌)),
            g c ≫ V.map (SSet.stdSimplex.objEquiv s.val).op = p c ≫ f m s := by
  classical
  let I := FormalCoproduct.incl.{u} X.Etale
  let K := V ⋙ I
  have hK : Scheme.IsSemiRepresentableHypercover K :=
    isSemiRepresentableHypercover_of_isEtaleHypercover V hV
  obtain ⟨hB, hBfin, _, ⟨uB, huB, hrepB⟩, _⟩ :=
    Scheme.simplicial_hom_standard_simplex K n
  let _ : SSet.Finite (Δ[n] : SSet.{t}) := hBfin
  have hAfin (m : ℕ) : Finite (A.toSSet.obj (op ⦋m⦌)) := by infer_instance
  obtain ⟨H, u, hu, hrep⟩ := Scheme.exists_simplicial_hom_object X K A.toSSet hAfin hAnonempty
  let uA : Scheme.SimplicialHomFamily K A.toSSet H := ⟨u, hu⟩
  have hrepA : (Scheme.simplicialHomFamilyFunctor K A.toSSet).IsRepresentedBy uA := by
    constructor
    intro W
    constructor
    · intro a b hab
      have ha : ∀ m s, a ≫ u m s = b ≫ u m s := by
        intro m s
        exact congrArg (fun z : Scheme.SimplicialHomFamily K A.toSSet W ↦ z.val m s) hab
      obtain ⟨g, hg, hguniq⟩ := hrep W (fun m s ↦ b ≫ u m s)
        (by intro m k φ s; rw [Category.assoc, hu])
      exact (hguniq a ha).trans (hguniq b (fun _ _ ↦ rfl)).symm
    · intro z
      obtain ⟨g, hg, _⟩ := hrep W z.val z.property
      refine ⟨g, Subtype.ext ?_⟩
      funext m s
      exact hg m s
  let z : Scheme.SimplicialHomFamily K A.toSSet (I.obj T) :=
    ⟨fun m s ↦ I.map (f m s), by
      intro m k φ s
      change I.map (f k s) ≫ I.map (V.map φ.op) = _
      rw [← I.map_comp, hf]⟩
  obtain ⟨a, ha⟩ := hrepA.map_bijective.surjective z
  obtain ⟨ι, Tc, p, hp, b, hb⟩ :=
    (Scheme.hypercover_finite_simplex_lifting X K hK (Δ[n]) A
      (fun m ↦ (hB m).1) (fun m ↦ (hB m).2) hAfin hAnonempty
      (K.obj (op ⦋n⦌)) H uB uA hrepB hrepA).2 T a
  refine ⟨ι, Tc, p, hp, fun c ↦ I.preimage (b c), ?_⟩
  intro c m s
  apply I.map_injective
  rw [I.map_comp, I.map_comp, I.map_preimage]
  have hρ : Scheme.simplicialHomRestriction A uB hrepA ≫ u m s = uB.val m s.val := by
    have hh := (Equiv.ofBijective _ hrepA.map_bijective).apply_symm_apply (uB.restrict A)
    exact congrArg (fun z : Scheme.SimplicialHomFamily K A.toSSet (K.obj (op ⦋n⦌)) ↦
      z.val m s) hh
  have hz : a ≫ u m s = I.map (f m s) :=
    congrArg (fun z : Scheme.SimplicialHomFamily K A.toSSet (I.obj T) ↦ z.val m s) ha
  rw [show I.map (V.map (SSet.stdSimplex.objEquiv s.val).op) = uB.val m s.val from
    (huB m s.val).symm]
  rw [← hρ, ← Category.assoc, hb, Category.assoc, hz]

end AlgebraicGeometry.EtaleSimplicialMatching
