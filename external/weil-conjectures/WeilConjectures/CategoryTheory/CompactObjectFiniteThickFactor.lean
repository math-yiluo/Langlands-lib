/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.CompactObject
public import Mathlib.CategoryTheory.Triangulated.Generators
public import WeilConjectures.CategoryTheory.WeakTriangulatedGenerator
import WeilConjectures.CategoryTheory.CompactGeneratorsBuildObjects
import WeilConjectures.CategoryTheory.CompactFactorThroughThick
import WeilConjectures.CategoryTheory.CompactHomHocolim
import Mathlib.CategoryTheory.Functor.OfSequence

/-! Abstract compact-to-thick factorization for a compact generating family.

Source: Stacks Project Tags 09SN, 09SP, and 094A, exactly the telescope and finite-stage
factorization paragraphs of `proposition-compactness-finite-coefficients`.
(blueprint: det-ctf-finite-compact-thick-factor)
-/

@[expose] public section
set_option autoImplicit false
universe w u
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory

/-- A compact object in a category built by a compact generating family retracts from a finite
thick envelope of that family.

Source: `proposition-compactness-finite-coefficients`, compact objects paragraph, Stacks Tags
09SN, 094A and 09SP (blueprint: det-ctf-finite-compact-thick-factor).

Proof: write the object as the telescope of extensions of coproducts of shifted generators.
Compact Hom commutes with this telescope, so its identity comes from a map into one stage.
Factor that map through an object in the thick envelope of a finite generator sum. Composing
the second factor with the telescope stage map supplies the retraction. This includes the
empty finite support and zero object cases. -/
theorem compact_mem_finite_thick_of_generators
    {C : Type u} [Category.{w} C] [HasZeroObject C] [HasShift C ℤ]
    [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]
    [Pretriangulated C] [IsTriangulated C] [HasCoproducts.{w} C]
    {I : Type w} (E : I → C) (hcompact : ∀ i, IsCompactObject (E i))
    (hgenerate : IsTriangulatedGeneratingFamily E)
    (K : C) (hK : IsCompactObject K) :
    ∃ (S : Finset I) (Q : C),
      (ObjectProperty.singleton
        (∐ fun i : {i : I // i ∈ S} ↦ E i.1)).triangEnvelope Q ∧
      Nonempty (Retract K Q) := by
  classical
  obtain ⟨X, t, hstart, hsteps, q, r, hT⟩ :=
    compactGenerators_buildObjects.{w, w} E hcompact hgenerate K
  let F := Functor.ofSequence t
  have hTF : Pretriangulated.Triangle.mk
      (𝟙 (∐ fun n : ULift.{w} ℕ ↦ F.obj n.down) -
        Sigma.desc (fun n : ULift.{w} ℕ ↦
          F.map (homOfLE (Nat.le_succ n.down)) ≫
            Sigma.ι (fun k : ULift.{w} ℕ ↦ F.obj k.down) ⟨n.down + 1⟩))
      q r ∈ distTriang C := by
    simpa [F, Functor.ofSequence, Functor.OfSequence.map_le_succ] using hT
  obtain ⟨φ, hφ, hbij⟩ := compact_hom_hocolim K hK F K q r hTF
  obtain ⟨z, hz⟩ := hbij.2 (𝟙 K)
  obtain ⟨n, a, ha⟩ := Types.jointly_surjective' z
  have hf : a ≫ Sigma.ι (fun k : ULift.{w} ℕ ↦ X k.down) ⟨n⟩ ≫ q = 𝟙 K := by
    rw [← hz, ← ha, hφ]
    rfl
  obtain ⟨S, Q, α, β, hQ, hαβ⟩ := compact_factorThrough_thickClosure
    E hcompact X t hstart hsteps K hK n a
  refine ⟨S, Q, hQ, ⟨⟨α, β ≫ Sigma.ι (fun k : ULift.{w} ℕ ↦ X k.down) ⟨n⟩ ≫ q,
    ?_⟩⟩⟩
  rw [← Category.assoc α β, hαβ]
  exact hf

end CategoryTheory
