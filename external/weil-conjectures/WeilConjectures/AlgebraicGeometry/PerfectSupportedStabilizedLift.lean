/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import Mathlib.AlgebraicGeometry.AffineScheme
import WeilConjectures.AlgebraicGeometry.SupportedMapInitialAmbientLift
import WeilConjectures.AlgebraicGeometry.SupportedMapAffineAttachment

/-! # The finite stabilization construction for supported map lifting

Source: Stacks Project, Tag 09IM, proof of Lemma 36.13.11.
(blueprint: lem-sc-perfect-supported-stabilized-lift).
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

private theorem stabilized_biprod_fst_comparison
    {C : Type*} [Category C] [HasZeroMorphisms C] [HasBinaryBiproducts C]
    {A B A' B' N P E : C} (e : A ≅ A') (s : B ≅ B')
    (d : N ≅ A ⊞ B) (h : P ≅ A' ⊞ B')
    (f : A ⟶ E) (a : A' ⟶ E) (b : P ⟶ E) (g : N ⟶ E)
    (hf : f = e.hom ≫ a) (hg : g = d.hom ≫ biprod.fst ≫ f)
    (hb : b = h.hom ≫ biprod.fst ≫ a) :
    g = (d ≪≫ biprod.mapIso e s ≪≫ h.symm).hom ≫ b := by
  rw [hg, hf, hb]
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id_assoc, biprod.mapIso_hom, biprod.map_fst_assoc]

set_option backward.isDefEq.respectTransparency false in
/-- The affine-cover construction extends one finite stabilization of the given map.
This records the actual iterated object and its first-projection map.
Source: Stacks Project, Tag 09IM, proof of Lemma 36.13.11 and Remark 36.13.12.
(blueprint: lem-sc-perfect-supported-stabilized-lift).

Proof: Choose finitely many affine opens whose union with U is X, and attach them
one at a time. Start with S 0 and a 0 on U. At an attachment V, the intersection
with the previously attached union is quasi-compact by quasi-separatedness.
The complement of T on V is quasi-compact for the same reason. Apply the affine
supported extension lemma to the current perfect object on that intersection;
it extends that object plus its shift to a perfect object Q on V supported on T.
Compose the overlap identification with the first projection and the current map.
Apply affine perfect map lifting to Q; its tensor augmentation is invertible on
the overlap, and its source remains perfect and supported on T. Glue the resulting
map on V to the first-projection map on the previous union by derived open gluing.
The two maps agree by the affine lifting equation. Perfectness and support are
local, so the glued source has both properties. On U the source and map have
changed from S k and a k to S (k+1) and a (k+1), using hS and ha. The canonical
comparison isomorphisms for iterated restriction transport these identifications.
Induction on the finite cover gives n, R, beta and the stated isomorphism and
map equation. No retraction or direct-summand assertion is used in this construction.
For an empty added cover use n=0; empty support or a zero source causes no change
in the construction. -/
theorem exists_perfect_supported_stabilized_lift
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (U : X.Opens) (hU : IsCompact (U : Set X))
    (T : Set X) (hT : IsClosed T) (hTc : IsCompact Tᶜ)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ V : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over V))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    [∀ V : U.toScheme.Opens,
      HasDerivedCategory.{w}
        (SheafOfModules.{u} ((moduleRings U.toScheme.toRingedSpace).over V))]
    (E : schemeDerivedQCohCategory X)
    (S : ℕ → schemeDerivedCategory U.toScheme)
    (hS : ∀ n : ℕ, S (n + 1) ≅ S n ⊞ (S n)⟦(1 : ℤ)⟧)
    (hP : IsPerfect U.toScheme (S 0))
    (hPT : ∀ (n : ℤ) (x : U.toScheme), x.val ∉ T →
      Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) n).obj
          (S 0)).val.presheaf x)))
    (a : ∀ n : ℕ, S n ⟶ ((SheafOfModules.overFunctor.{u}
        (moduleRings X.toRingedSpace) U) ⋙ Equivalence.functor
          (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
            (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
          (Modules.overEquiv U)).mapDerivedCategory.obj E.obj)
    (ha : ∀ n : ℕ, a (n + 1) = (hS n).hom ≫ biprod.fst ≫ a n) :
    ∃ (n : ℕ) (R : schemeDerivedCategory X) (β : R ⟶ E.obj),
      IsPerfect X R ∧
      (∀ (i : ℤ) (x : X), x ∉ T →
        Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) i).obj R).val.presheaf x))) ∧
      ∃ e : ((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U) ⋙
          Equivalence.functor
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
            (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
            (Modules.overEquiv U)).mapDerivedCategory.obj R ≅ S n,
        ((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U) ⋙
          Equivalence.functor
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
            (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
            (Modules.overEquiv U)).mapDerivedCategory.map β = e.hom ≫ a n := by
  classical
  let P (W : X.Opens) : Prop :=
    ∃ (n : ℕ) (R : schemeDerivedCategory X) (β : R ⟶ E.obj),
      (∀ x : X, x ∈ W → ∃ O : X.Opens, x ∈ O ∧
        ∃ K : CochainComplex
            (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over O)) ℤ,
          IsStrictlyPerfect X O K ∧
          Nonempty ((SheafOfModules.overFunctor.{u}
            (moduleRings X.toRingedSpace) O).mapDerivedCategory.obj R ≅
              DerivedCategory.Q.obj K)) ∧
      (∀ (i : ℤ) (x : X), x ∈ W → x ∉ T →
        Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) i).obj R).val.presheaf x))) ∧
      ∃ e : ((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U) ⋙
          Equivalence.functor
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
            (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
            (Modules.overEquiv U)).mapDerivedCategory.obj R ≅ S n,
        ((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U) ⋙
          Equivalence.functor
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
            (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
            (Modules.overEquiv U)).mapDerivedCategory.map β = e.hom ≫ a n
  have hbase : P U := by
    obtain ⟨R, β, hR, hRT, e, he⟩ :=
      exists_supported_map_initial_ambient_lift X U T E (S 0) hP hPT (a 0)
    exact ⟨0, R, β, hR, hRT, e, he⟩
  have hstep (W : X.Opens) (hUW : U ≤ W) (hW : IsCompact (W : Set X))
      (V : X.affineOpens) (hPW : P W) : P (W ⊔ V.val) := by
    obtain ⟨n, R, β, hR, hRT, e, he⟩ := hPW
    obtain ⟨R', β', hR', hRT', e', he'⟩ :=
      exists_supported_map_affine_attachment X U W V.val hUW hW V.property T hT hTc
        E R β hR hRT
    let d := biprod.mapIso e
      ((shiftFunctor (schemeDerivedCategory U.toScheme) (1 : ℤ)).mapIso e)
    refine ⟨n + 1, R', β', hR', hRT', e' ≪≫ d ≪≫ (hS n).symm, ?_⟩
    exact stabilized_biprod_fst_comparison e
      ((shiftFunctor (schemeDerivedCategory U.toScheme) (1 : ℤ)).mapIso e)
      e' (hS n) _ (a n) (a (n + 1)) _ he he' (ha n)
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun V : X.affineOpens ↦ (V.val : Set X)) (fun V ↦ V.val.isOpen) (by
      intro x _
      obtain ⟨V, hV, hx, _⟩ := exists_isAffineOpen_mem_and_subset
        (show x ∈ (⊤ : X.Opens) from trivial)
      exact Set.mem_iUnion.mpr ⟨⟨V, hV⟩, hx⟩)
  have hind (t : Finset X.affineOpens) :
      IsCompact ((U ⊔ ⨆ V ∈ t, V.val : X.Opens) : Set X) ∧
        P (U ⊔ ⨆ V ∈ t, V.val) := by
    induction t using Finset.induction_on with
    | empty => simpa using And.intro hU hbase
    | @insert V t hV ih =>
      have hUW : U ≤ U ⊔ ⨆ V ∈ t, V.val := le_sup_left
      have hp := hstep _ hUW ih.1 V ih.2
      have hc : IsCompact
          (((U ⊔ ⨆ V ∈ t, V.val) ⊔ V.val : X.Opens) : Set X) :=
        ih.1.union V.property.isCompact
      simpa only [Finset.iSup_insert, sup_assoc, sup_comm, sup_left_comm] using
        And.intro hc hp
  have hcover : (U ⊔ ⨆ V ∈ s, V.val : X.Opens) = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨V, hV, hx⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ x))
    have hx' : x ∈ (⨆ V ∈ s, V.val : X.Opens) := by
      simp only [TopologicalSpace.Opens.mem_iSup]
      exact ⟨V, hV, hx⟩
    exact (le_sup_right : (⨆ V ∈ s, V.val : X.Opens) ≤ U ⊔ ⨆ V ∈ s, V.val) hx'
  have htop : P ⊤ := by simpa only [hcover] using (hind s).2
  obtain ⟨n, R, β, hR, hRT, e, he⟩ := htop
  refine ⟨n, R, β, ?_, ?_, e, he⟩
  · exact fun x ↦ hR x trivial
  · exact fun i x hx ↦ hRT i x trivial hx

end AlgebraicGeometry.Scheme
