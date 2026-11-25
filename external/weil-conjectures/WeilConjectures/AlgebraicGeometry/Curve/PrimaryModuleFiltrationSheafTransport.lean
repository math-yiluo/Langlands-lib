/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RepresentationTheory.DiscreteContinuousRep
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.Topology.Algebra.OpenSubgroup
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer

import WeilConjectures.AlgebraicGeometry.Curve.PrimaryModuleFiltrationSheafExactness
import WeilConjectures.AlgebraicGeometry.Curve.PrimaryModuleFiltrationConstantQuotient
import WeilConjectures.AlgebraicGeometry.Curve.PrimaryModuleFiltrationInverseImage

/-!
# Transport of an invariant primary module filtration to etale sheaves

Source: the generic-filtration argument in blueprint `theorem-cohomology-curves--2`,
proof paragraphs 1--2; Stacks Project, Tags 04JQ, 03QT and 03SF.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits ZeroObject Opposite


namespace AlgebraicGeometry.Scheme

set_option linter.unusedVariables false

/-- Transport a supplied invariant subgroup chain, rather than construct a Sylow chain.
Source: blueprint `theorem-cohomology-curves--2`, proof paragraphs 1--2;
Stacks Project, Tags 04JQ, 03QT and 03SF.
(blueprint: lem-sc-primary-module-filtration-sheaf-transport)

Proof: Regard every subgroup in the chain as an integer submodule; additive subgroups
are automatically stable under integer scalar multiplication. Restrict the representation
to H. The stability hypotheses give continuous discrete actions on the submodules and
quotients, since stabilizers contain the corresponding open stabilizers in the ambient
module. The chain inclusions and quotient maps are equivariant and form short exact
sequences. Each quotient is finite, killed by ell, and has trivial H-action by the two
successor hypotheses. Give it its canonical ZMod ell vector space structure and choose
a finite basis, identifying it with a finite direct sum of copies of ZMod ell.
The field L fixed by H has absolute Galois group H. Under the equivalence between
abelian etale sheaves and discrete Galois modules, inverse image from Spec K to Spec L
is restriction to H: on germs it leaves a section unchanged, and the displayed action
compatibility identifies its monodromy with the restricted action. Transport the
submodules and their short exact sequences through this equivalence. Equivalences
preserve zero objects, exactness and finite biproducts, and trivial modules correspond
to constant sheaves. The bottom and top terms give zero and the inverse image of M.
Finally pull everything across the scheme isomorphism e, and use composition of
inverse images and preservation of constant sheaves. For the natural-number indexing,
use the given chain on indices at most n and its last term on all larger indices.
This also treats n = 0: the bottom and top equalities force the module to be zero. -/
theorem exists_sheaf_filtration_of_invariant_primary_chain
    (K Ks Ω : Type u) [Field K] [Field Ks] [Field Ω]
    [Algebra K Ks] [IsSepClosure K Ks] [Algebra Ks Ω] [Algebra K Ω]
    [IsScalarTower K Ks Ω] [IsAlgClosed Ω]
    (M : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (R : Rep.DiscreteContinuousRep.{0, u, u + 1} ℤ (Gal(Ks/K)))
    (i : AddCommGrpCat.of R.obj.V ≅
      ((pointSmallEtale (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).sheafFiber
        (A := AddCommGrpCat.{u + 1})).obj M)
    (haction : ∀ (g : Gal(Ks/K)) (τ : Ω ≃ₐ[K] Ω)
      (hτ : (algebraMap Ks Ω).comp g.toRingHom =
        τ.toRingHom.comp (algebraMap Ks Ω))
      (X : (Spec (.of K)).Etale)
      (x x' : (pointSmallEtale
        (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).fiber.obj X)
      (hx : x'.left = Spec.map (CommRingCat.ofHom τ.toRingHom) ≫ x.left)
      (z : M.obj.obj (op X)),
      i.hom (R.obj.ρ g (i.inv ((pointSmallEtale
        (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).toPresheafFiber X x M.obj z))) =
      (pointSmallEtale (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).toPresheafFiber
        X x' M.obj z)
    (ℓ : ℕ) (hℓ : ℓ.Prime) [Finite R.obj.V]
    (H : OpenSubgroup (Gal(Ks/K)))
    [FiniteDimensional K (IntermediateField.fixedField H.toSubgroup)]
    (n : ℕ) (A : Fin (n + 1) → AddSubgroup R.obj.V)
    (hmono : Monotone A) (hzero : A 0 = ⊥) (htop : A (Fin.last n) = ⊤)
    (hstable : ∀ (a : Fin (n + 1)) (g : H) (x : R.obj.V),
      x ∈ A a → R.obj.ρ (g : Gal(Ks/K)) x ∈ A a)
    (hstep : ∀ (a : Fin n) (x : R.obj.V), x ∈ A a.succ →
      ℓ • x ∈ A a.castSucc ∧ ∀ g : H, R.obj.ρ (g : Gal(Ks/K)) x - x ∈ A a.castSucc)
    (T : Scheme.{u}) (e : Spec (.of (IntermediateField.fixedField H.toSubgroup)) ≅ T) :
    ∃ F : ℕ → Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1},
      IsZero (F 0) ∧
      (∀ a : ℕ, a < n →
        ∃ (S : ShortComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})) (d : ℕ),
          S.ShortExact ∧ Nonempty (S.X₁ ≅ F a) ∧ Nonempty (S.X₂ ≅ F (a + 1)) ∧
          Nonempty (S.X₃ ≅ Nat.rec (0 : _)
            (fun _ B ↦ B ⊞ T.constantZMod ℓ) d)) ∧
      Nonempty ((Etale.upperStar AddCommGrpCat.{u + 1}
        (e.inv ≫ Spec.map (CommRingCat.ofHom
          (algebraMap K (IntermediateField.fixedField H.toSubgroup))))).obj M ≅ F n) := by
  obtain ⟨C, hC⟩ := nonempty_primaryFixedFieldComparison K Ks H Ω
  let idx (a : ℕ) : Fin (n + 1) := ⟨min a n, by omega⟩
  let F (a : ℕ) := primaryAssociatedSheaf K Ks H Ω C T e
    (primarySubmodule K Ks H R (A (idx a)) (hstable (idx a)))
  have hidx0 : idx 0 = 0 := Fin.ext (Nat.zero_min n)
  have hidxn : idx n = Fin.last n := Fin.ext (Nat.min_self n)
  refine ⟨F, ?_, ?_, ?_⟩
  · apply primaryAssociatedSheaf_zero K Ks H Ω C T e R (A (idx 0))
    simpa only [hidx0] using hzero
  · intro a ha
    let b : Fin n := ⟨a, ha⟩
    have hidxa : idx a = b.castSucc := Fin.ext (Nat.min_eq_left ha.le)
    have hidxs : idx (a + 1) = b.succ := Fin.ext (Nat.min_eq_left ha)
    have hle : A b.castSucc ≤ A b.succ := hmono (by simp [Fin.le_iff_val_le_val])
    obtain ⟨hS, ⟨jQ⟩⟩ := primarySheafSequence_shortExact K Ks Ω H C hC T e R
      (A b.castSucc) (A b.succ) hle (hstable b.castSucc) (hstable b.succ)
      (fun g x hx ↦ (hstep b x hx).2 g)
    obtain ⟨d, ⟨jconst⟩⟩ := primaryTrivialQuotient_constant K Ks Ω H C hC T e R
      (A b.castSucc) (A b.succ) ℓ hℓ (fun x hx ↦ (hstep b x hx).1)
    refine ⟨primarySheafSequence K Ks H Ω C T e R (A b.castSucc) (A b.succ)
      hle (hstable b.castSucc) (hstable b.succ), d, hS, ?_, ?_, ⟨jQ ≪≫ jconst⟩⟩
    · change Nonempty (primaryAssociatedSheaf K Ks H Ω C T e
        (primarySubmodule K Ks H R (A b.castSucc) (hstable b.castSucc)) ≅ F a)
      dsimp [F]
      rw [hidxa]
      exact ⟨Iso.refl _⟩
    · change Nonempty (primaryAssociatedSheaf K Ks H Ω C T e
        (primarySubmodule K Ks H R (A b.succ) (hstable b.succ)) ≅ F (a + 1))
      dsimp [F]
      rw [hidxs]
      exact ⟨Iso.refl _⟩
  · obtain ⟨jM⟩ := primary_inverseImage_restriction K Ks Ω M R i haction H C hC T e
    have htop' : A (idx n) = ⊤ := hidxn ▸ htop
    obtain ⟨jtop⟩ := primarySubmoduleTopIso K Ks H R (A (idx n)) htop' (hstable (idx n))
    exact ⟨jM ≪≫ (Etale.upperStar AddCommGrpCat.{u + 1} e.inv).mapIso
      (C.inverse.mapIso jtop.symm)⟩

end AlgebraicGeometry.Scheme
