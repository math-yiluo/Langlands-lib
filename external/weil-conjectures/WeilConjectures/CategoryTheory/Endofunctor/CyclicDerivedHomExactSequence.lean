/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Endofunctor.CyclicDerivedHomData
import WeilConjectures.CategoryTheory.Endofunctor.CyclicDerivedOffDiagonalCalculus
import WeilConjectures.CategoryTheory.Endofunctor.CyclicDerivedExactAction
import WeilConjectures.CategoryTheory.Endofunctor.CyclicDerivedExactPresentation
import WeilConjectures.CategoryTheory.Endofunctor.CyclicDerivedRightAction
import WeilConjectures.CategoryTheory.Endofunctor.CyclicDerivedRightPresentation
import WeilConjectures.CategoryTheory.Exact.ExactInputDerivedTransformation

/-! # Native derived morphisms of fixed pairs

Proofs of the cyclic invariant/coinvariant sequence and its functoriality.
Source: Stacks Project, Derived Categories, Tags 0149, 0152, 070I.
(blueprint: lem-sf-cyclic-derived-hom-exact-sequence).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w wF uD vD wD wG

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Endofunctor.IsoAlgebra

variable {C : Type u} [Category.{v} C] [Abelian C]
  (F : C ⥤ C) [F.Additive] [F.IsEquivalence]
  [HasDerivedCategory.{w} C] [HasDerivedCategory.{wF} (IsoAlgebra F)]

private theorem normalized_boundary_on_presentation
    (b : CyclicDerivedHomBoundary F) (hb : CyclicDerivedHomBoundaryNormalized F b)
    (hn : CyclicDerivedHomBoundaryNatural F b)
    {M N : DerivedCategory (IsoAlgebra F)}
    (hM : DerivedCategory.TStructure.t.bounded M)
    (hN : DerivedCategory.TStructure.t.bounded N)
    {u : CyclicDerivedHom F M N (-1)} {f : M ⟶ N}
    (hp : CyclicDerivedOffDiagonalPresentation F u f) :
    b M N hM hN (QuotientAddGroup.mk u) = f := by
  obtain ⟨S, hS, u₀, s, a, c, hs, he, hu, hf⟩ := hp
  have hM₀ := DerivedCategory.TStructure.t.bounded.prop_of_iso a hM
  have hN₀ := DerivedCategory.TStructure.t.bounded.prop_of_iso c.symm hN
  have hnorm := hb S hS hM₀ hN₀ u₀ s hs he
  have hnat := hn _ _ M N hM₀ hN₀ hM hN a.hom c.hom
    (cyclicDerivedOffDiagonalClass F u₀)
  rw [hnorm, ← hu] at hnat
  exact hnat.symm.trans hf.symm

/-- The invariant/coinvariant sequence with its canonical boundary and naturality.

Proof plan, following node steps 1--8 and the uniqueness implicit in its normalization:
1. Use lem-sf-free-derived-weil-resolution: the exact free/forgetful adjunction gives
   the natural triangle IUM → IUM → M → IUM[1], with the specified summand formula.
2. Under adjunction, the component of an adjunct at summand n is the iterated structure
   map composed with P^n(u). Evaluating the differential at summand zero gives
   1-(T^r)⁻¹, and the counit gives precisely the forgetting map.
3. Apply lem-weil-pbc-hom-out-of-triangle-exact and rotations to obtain the five-term
   Hom segment in degrees -1 and 0, with boundary u ↦ u_tilde[1] δ_M.
4. The identity 1-T⁻¹ = -T⁻¹(1-T) identifies the actual kernels and images. Factor through
   the actual quotient and subgroup, retaining the free-resolution sign, to get exactness.
5. Naturality of the free triangle and adjunction gives the pre/postcomposition square;
   localization of the fixed-pair equation gives commutation with T.
6. By enough injectives, lem-weil-pbc-dplus-injective-representative and the K-injective
   Hom and shift lemmas, represent a degree-minus-one underlying morphism by a chain
   map u: UJ → UA, with A representing N[-1].
7. On UA ⊕ UJ put the triangular action with diagonal θ_A, θ_J and upper entry θ_A P(u).
   Its inverse has upper entry -P(u)θ_J⁻¹. Inclusion and projection give a short exact
   fixed-pair sequence with a split underlying chain sequence.
8. In the free comparison let s be the second inclusion, e its adjunct and f the adjunct
   of u. Evaluation at summand zero gives ed_J=jf and pe=ε_J. Naturality of the canonical
   SES boundary (lem-weil-pbc-complex-ses-triangle; Stacks Tag 0152) identifies its boundary
   with f[1]δ_J. Thus it has exactly the required normalization. Every quotient class has
   such a representative. Naturality and this formula force uniqueness after transport
   along the representing isomorphisms. No derived faithfulness claim is used.

Source: cor-coef-verdier-weil-equivariance.proof.md, final exceptional-adjunction sentence; the
DAG node's agent-formulated native-derived expansion, proof steps 1--12; Stacks derived.tex,
Tags 0149, 0152 and 070I.
(blueprint: lem-sf-cyclic-derived-hom-exact-sequence). -/
theorem exists_cyclicDerivedHomBoundary [IsGrothendieckAbelian.{v} C] :
    ∃! b : CyclicDerivedHomBoundary F,
      CyclicDerivedHomBoundaryExact F b ∧ CyclicDerivedHomBoundaryNatural F b ∧
        CyclicDerivedHomBoundaryNormalized F b := by
  classical
  let d := cyclicDerivedOffDiagonalBoundaryHom F
  have hd (M N : DerivedCategory (IsoAlgebra F)) :
      (cyclicDerivedHomDefect F M N (-1)).range = (d M N).ker := by
    ext u
    exact ((cyclicDerivedOffDiagonal_calculus F).2.1 M N).1 u |>.symm
  let b : CyclicDerivedHomBoundary F := fun M N _ _ ↦
    QuotientAddGroup.lift _ (d M N) (hd M N).le
  refine ⟨b, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro M N hM hN
    have hex := (cyclicDerivedOffDiagonal_calculus F).2.1 M N
    let q : (M ⟶ N) →+ CyclicDerivedHomInvariants F M N :=
      (cyclicDerivedForget F M N).codRestrict _ (fun f ↦
        hex.2.2.apply_apply_eq_zero f)
    refine ⟨q, fun _ ↦ rfl, ?_, ?_, ?_⟩
    · exact (QuotientAddGroup.injective_lift_iff _ _ _).2 (hd M N)
    · intro f
      rw [show q f = 0 ↔ cyclicDerivedForget F M N f = 0 from
        ⟨fun h ↦ congrArg Subtype.val h, fun h ↦ Subtype.ext h⟩, hex.2.1 f]
      constructor
      · rintro ⟨u, rfl⟩
        exact ⟨QuotientAddGroup.mk u, rfl⟩
      · rintro ⟨u, hu⟩
        obtain ⟨u, rfl⟩ := QuotientAddGroup.mk_surjective u
        exact ⟨u, hu⟩
    · intro u
      obtain ⟨f, hf⟩ := (hex.2.2 u.val).1 u.property
      exact ⟨f, Subtype.ext hf⟩
  · intro M N M' N' hM hN hM' hN' a c u
    exact (cyclicDerivedOffDiagonal_calculus F).2.2 M N M' N' a c u
  · intro S hS hM hN u s hs he
    apply cyclicDerivedOffDiagonalBoundary_eq F
    refine ⟨S, hS, u, s, Iso.refl _, Iso.refl _, hs, he, ?_, ?_⟩
    · simp
    · simp
  · intro b' hb'
    funext M N hM hN
    apply AddMonoidHom.ext
    intro u
    obtain ⟨u, rfl⟩ := QuotientAddGroup.mk_surjective u
    exact normalized_boundary_on_presentation F b' hb'.2.2 hb'.2.1 hM hN
      (cyclicDerivedOffDiagonalBoundary_presentation F u)

variable {D : Type uD} [Category.{vD} D] [Abelian D]
  (G : D ⥤ D) [G.Additive] [G.IsEquivalence]
  [HasDerivedCategory.{wD} D] [HasDerivedCategory.{wG} (IsoAlgebra G)]

private theorem transport_additive
    (J : DerivedCategory (IsoAlgebra F) ⥤ DerivedCategory (IsoAlgebra G))
    (H : DerivedCategory C ⥤ DerivedCategory D) [H.Additive]
    (σ : ∀ r : ℤ, shiftFunctor (DerivedCategory C) r ⋙ H ≅
      H ⋙ shiftFunctor (DerivedCategory D) r)
    (α : J ⋙ (forget G).mapDerivedCategory ≅ (forget F).mapDerivedCategory ⋙ H)
    (M N : DerivedCategory (IsoAlgebra F)) (r : ℤ) :
    cyclicDerivedHomTransport F G J H σ α M N r 0 = 0 ∧
      ∀ u v : CyclicDerivedHom F M N r,
        cyclicDerivedHomTransport F G J H σ α M N r (u + v) =
          cyclicDerivedHomTransport F G J H σ α M N r u +
            cyclicDerivedHomTransport F G J H σ α M N r v := by
  constructor
  · simp [cyclicDerivedHomTransport]
  · intro u v
    simp [cyclicDerivedHomTransport, Preadditive.comp_add, Preadditive.add_comp]

private theorem transport_forget
    (J : DerivedCategory (IsoAlgebra F) ⥤ DerivedCategory (IsoAlgebra G))
    (H : DerivedCategory C ⥤ DerivedCategory D) [H.CommShift ℤ]
    (α : J ⋙ (forget G).mapDerivedCategory ≅ (forget F).mapDerivedCategory ⋙ H)
    {M N : DerivedCategory (IsoAlgebra F)} (f : M ⟶ N) :
    cyclicDerivedHomTransport F G J H (fun r ↦ H.commShiftIso r) α M N 0
        (cyclicDerivedForget F M N f) =
      cyclicDerivedForget G (J.obj M) (J.obj N) (J.map f) := by
  change α.hom.app M ≫
    H.map ((forget F).mapDerivedCategory.map f ≫
      (shiftFunctorZero (DerivedCategory C) ℤ).inv.app _) ≫
    (H.commShiftIso (0 : ℤ)).hom.app _ ≫ (α.inv.app N)⟦(0 : ℤ)⟧' =
      (forget G).mapDerivedCategory.map (J.map f) ≫
        (shiftFunctorZero (DerivedCategory D) ℤ).inv.app _
  simp only [Functor.map_comp, Functor.commShiftIso_zero,
    Functor.CommShift.isoZero_hom_app, Category.assoc]
  simp only [← H.map_comp_assoc, Iso.inv_hom_id_app]
  have hc : (forget F).mapDerivedCategory.map f ≫
      𝟙 ((𝟭 (DerivedCategory C)).obj ((forget F).mapDerivedCategory.obj N)) =
        (forget F).mapDerivedCategory.map f := Category.comp_id _
  rw [hc]
  have hz :
      (shiftFunctorZero (DerivedCategory D) ℤ).inv.app
          (H.obj ((forget F).mapDerivedCategory.obj N)) ≫ (α.inv.app N)⟦(0 : ℤ)⟧' =
        α.inv.app N ≫ (shiftFunctorZero (DerivedCategory D) ℤ).inv.app
          ((forget G).mapDerivedCategory.obj (J.obj N)) := by
    simpa only [Functor.id_obj, Functor.id_map, Functor.comp_obj] using
      ((shiftFunctorZero (DerivedCategory D) ℤ).inv.naturality (α.inv.app N)).symm
  rw [hz]
  have ha : (forget G).mapDerivedCategory.map (J.map f) ≫ α.hom.app N =
      α.hom.app M ≫ H.map ((forget F).mapDerivedCategory.map f) :=
    α.hom.naturality f
  rw [← Category.assoc, ← ha, Category.assoc, Iso.hom_inv_id_app_assoc]

private theorem rightDerived_shifts
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    {B : Type uD} [Category.{vD} B] [Abelian B] [HasDerivedCategory.{wD} B]
    (H : A ⥤ B) [H.Additive]
    (h : ∀ K : CochainComplex A ℤ,
      ∃ (I : CochainComplex A ℤ) (s : K ⟶ I), I.IsKInjective ∧ QuasiIso s) :
    ∃ s : (H.rightDerivedFunctorOfQuasiIsoResolutions h).CommShift ℤ,
      (fun [_s : (H.rightDerivedFunctorOfQuasiIsoResolutions h).CommShift ℤ] ↦
        NatTrans.CommShift (H.rightDerivedFunctorOfQuasiIsoResolutionsUnit h) ℤ ∧
        (H.rightDerivedFunctorOfQuasiIsoResolutions h).IsTriangulated) (_s := s) := by
  obtain ⟨s, s', hs, hs', htri, _⟩ :=
    Functor.exists_unique_exactInputDerivedTransformation (𝟭 A) H H h h
      (Functor.leftUnitor H).inv
  exact ⟨s, hs, htri⟩

variable (L : C ⥤ D) [L.Additive] (e : L ⋙ G ≅ F ⋙ L)

/-- Exact functors preserve the entire sequence, including its normalized boundary.

Proof plan, node steps 6--12 in the exact case:
1. Represent M and N by bounded-below complexes J,K of injectives in the fixed-pair
   category, using lem-weil-pbc-dplus-injective-representative. Forgetting preserves
   K-injectives by lem-sf-fixed-pair-derived-forget-comparison. The K-injective Hom
   and shift lemmas represent u by UJ → U(K[-1]).
2. Construct the off-diagonal extension A → E → J as above. Its degrees split in the
   fixed-pair category because A is termwise injective; E and the cone of its inclusion
   are bounded-below complexes of injectives, hence K-injective. The cone projection to
   J has contractible kernel, so it is a quasi-isomorphism by the cohomology long exact
   sequence and a homotopy equivalence by the K-injective Hom lemma.
3. Additivity preserves finite sums, shifts, cones and chain homotopies. An exact H
   acts termwise on the derived category (situation-conventions).
   The formula -Qπ (Qq)⁻¹ of Stacks Tag 0152 is consequently preserved, including its sign.
4. Naturality of e gives the new upper entry H(θ_A)e P′H(u); thus the image extension
   is precisely the normalized extension for the prescribed underlying morphism.
   The normalization predicates identify its boundary with the required target boundary.
5. The fixed-pair equation and the canonical comparison show additivity, T-compatibility,
   and the forgetting square. The two boundary naturality predicates transport these
   calculations from representatives to all native derived objects and morphisms.

Source: cor-coef-verdier-weil-equivariance.proof.md, final exceptional-adjunction sentence; the
DAG node's agent-formulated native-derived expansion, proof steps 1--12; Stacks derived.tex,
Tags 0149, 0152 and 070I.
(blueprint: lem-sf-cyclic-derived-hom-exact-sequence). -/
theorem cyclicDerivedHom_exact_functorial [IsGrothendieckAbelian.{v} C]
    [IsGrothendieckAbelian.{vD} D] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (b : CyclicDerivedHomBoundary F) (b' : CyclicDerivedHomBoundary G)
    (hb : CyclicDerivedHomBoundaryNormalized F b)
    (hb' : CyclicDerivedHomBoundaryNormalized G b')
    (hn : CyclicDerivedHomBoundaryNatural F b)
    (hn' : CyclicDerivedHomBoundaryNatural G b') :
    CyclicDerivedHomBoundaryFunctorial F G b b' (mapOfNatIso e).mapDerivedCategory
      L.mapDerivedCategory (fun r ↦ L.mapDerivedCategory.commShiftIso r)
        (cyclicDerivedExactForgetComparison F G L e) := by
  intro M N hM hN hJM hJN
  refine ⟨transport_additive F G _ _ _ _ M N, ?_, ?_, ?_⟩
  · intro r u
    exact cyclicDerivedHomTransport_exact_action F G L e M N r u
  · intro f
    exact transport_forget F G _ _ _ f
  · intro u
    have hp := cyclicDerivedOffDiagonalBoundary_presentation F u
    rw [normalized_boundary_on_presentation F b hb hn hM hN hp]
    exact (normalized_boundary_on_presentation G b' hb' hn' hJM hJN
      (cyclicDerivedOffDiagonalPresentation_mapExact F G L e hp)).symm

/-- Total right derived functors preserve the normalized connecting map.

Proof plan, node steps 6--12 in the left exact case:
1. Use bounded-below injective representatives and the off-diagonal extension as in the
   exact-functor proof. The injectivity extension property splits its degrees, so A,E,J
   and the cone are K-injective (def-sp-injective-resolutions and the dplus/K-injective
   nodes). The cone projection is a homotopy equivalence.
2. The recorded right-derived universal pair computes RH^eq on these representatives
   by H^eq. Its shift comparison is induced by shifting K-injective resolutions; the
   universal property makes it coherent and compatible with its unit. The same argument
   supplies the underlying shift comparison for RH (lem-pc-right-derived-functor-
   triangulated, transported to the arbitrary-resolution interface).
3. Additivity of H^eq preserves the degreewise split sequence, its cone, the cone
   projection and its homotopy inverse. The formula -Qπ (Qq)⁻¹ therefore proves preservation
   of the actual SES boundary, even when H^eq is not exact on arbitrary sequences.
4. The unique comparison of lem-sf-fixed-pair-derived-forget-comparison identifies both
   computations with H(UI), and has the identity normalization there. Naturality of e
   identifies the image off-diagonal entry with θ_FA P′H(u). Normalization of b and b′
   and their morphism naturality give the left square on the specified quotient class.
5. The same unit and shift comparisons give the induced maps on every V^r. Their
   additivity and T-compatibility give the prescribed outer maps, and forgetting gives
   the right square. Resolution witnesses are universally quantified proof choices;
   their existence is the Grothendieck K-injective theorem, not an added hypothesis.

Source: cor-coef-verdier-weil-equivariance.proof.md, final exceptional-adjunction sentence; the
DAG node's agent-formulated native-derived expansion, proof steps 1--12; Stacks derived.tex,
Tags 0149, 0152 and 070I.
(blueprint: lem-sf-cyclic-derived-hom-exact-sequence). -/
theorem cyclicDerivedHom_rightDerived_functorial [IsGrothendieckAbelian.{v} C]
    [IsGrothendieckAbelian.{vD} D] [PreservesFiniteLimits L]
    (hF : ∀ K : CochainComplex (IsoAlgebra F) ℤ,
      ∃ (I : CochainComplex (IsoAlgebra F) ℤ) (s : K ⟶ I), I.IsKInjective ∧ QuasiIso s)
    (hC : ∀ K : CochainComplex C ℤ,
      ∃ (I : CochainComplex C ℤ) (s : K ⟶ I), I.IsKInjective ∧ QuasiIso s)
    (b : CyclicDerivedHomBoundary F) (b' : CyclicDerivedHomBoundary G)
    (hb : CyclicDerivedHomBoundaryNormalized F b)
    (hb' : CyclicDerivedHomBoundaryNormalized G b')
    (hn : CyclicDerivedHomBoundaryNatural F b)
    (hn' : CyclicDerivedHomBoundaryNatural G b') :
    ∃ (sF : ((mapOfNatIso e).rightDerivedFunctorOfQuasiIsoResolutions hF).CommShift ℤ)
      (sC : (L.rightDerivedFunctorOfQuasiIsoResolutions hC).CommShift ℤ),
      (fun [_sF : ((mapOfNatIso e).rightDerivedFunctorOfQuasiIsoResolutions hF).CommShift ℤ]
        [_sC : (L.rightDerivedFunctorOfQuasiIsoResolutions hC).CommShift ℤ] ↦
        NatTrans.CommShift ((mapOfNatIso e).rightDerivedFunctorOfQuasiIsoResolutionsUnit hF) ℤ ∧
        NatTrans.CommShift (L.rightDerivedFunctorOfQuasiIsoResolutionsUnit hC) ℤ ∧
        CyclicDerivedHomBoundaryFunctorial F G b b'
          ((mapOfNatIso e).rightDerivedFunctorOfQuasiIsoResolutions hF)
          (L.rightDerivedFunctorOfQuasiIsoResolutions hC)
          (fun r ↦ (L.rightDerivedFunctorOfQuasiIsoResolutions hC).commShiftIso r)
          (cyclicDerivedRightForgetComparison F G L e hF hC)) (_sF := sF) (_sC := sC) := by
  obtain ⟨sF, hsF, htF⟩ := rightDerived_shifts (mapOfNatIso e) hF
  obtain ⟨sC, hsC, htC⟩ := rightDerived_shifts L hC
  let := sF
  let := sC
  let := htC
  refine ⟨sF, sC, hsF, hsC, ?_⟩
  intro M N hM hN hJM hJN
  refine ⟨transport_additive F G _ _ _ _ M N, ?_, ?_, ?_⟩
  · intro r u
    exact cyclicDerivedHomTransport_rightDerived_action F G L e hF hC hsC M N r u
  · intro f
    exact transport_forget F G _ _ _ f
  · intro u
    have hp := cyclicDerivedOffDiagonalBoundary_presentation F u
    rw [normalized_boundary_on_presentation F b hb hn hM hN hp]
    exact (normalized_boundary_on_presentation G b' hb' hn' hJM hJN
      (cyclicDerivedOffDiagonalPresentation_mapRightDerived F G L e hF hC hsC hp)).symm

end CategoryTheory.Endofunctor.IsoAlgebra

namespace CategoryTheory.Endofunctor.IsoAlgebra

private theorem transport_id
    (X : CyclicDerivedSetting.{u, v, w, wF})
    (M N : DerivedCategory (IsoAlgebra X.action)) (r : ℤ)
    (u : CyclicDerivedHom X.action M N r) :
    cyclicDerivedHomTransport X.action X.action (CyclicDerivedTransport.id X).native
      (CyclicDerivedTransport.id X).underlying (CyclicDerivedTransport.id X).shiftIso
      (CyclicDerivedTransport.id X).comparison M N r u = u := by
  simp [cyclicDerivedHomTransport, CyclicDerivedTransport.id,
    CyclicDerivedTransport.shiftIso]

private theorem transport_comp
    {X Y Z : CyclicDerivedSetting.{u, v, w, wF}}
    (s : CyclicDerivedTransport X Y) (t : CyclicDerivedTransport Y Z)
    (M N : DerivedCategory (IsoAlgebra X.action)) (r : ℤ)
    (u : CyclicDerivedHom X.action M N r) :
    cyclicDerivedHomTransport X.action Z.action (s.comp t).native
      (s.comp t).underlying (s.comp t).shiftIso (s.comp t).comparison M N r u =
    cyclicDerivedHomTransport Y.action Z.action t.native t.underlying t.shiftIso t.comparison
      (s.native.obj M) (s.native.obj N) r
      (cyclicDerivedHomTransport X.action Y.action s.native s.underlying s.shiftIso
        s.comparison M N r u) := by
  let := s.shifts
  let := t.shifts
  simp only [cyclicDerivedHomTransport, CyclicDerivedTransport.comp,
    CyclicDerivedTransport.shiftIso, Functor.commShiftIso_comp_hom_app,
    Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerRight_inv, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.comp_obj, Functor.comp_map, Functor.map_comp,
    Category.id_comp, Category.comp_id, Category.assoc]
  have hn := (t.underlying.commShiftIso r).hom.naturality (s.comparison.inv.app N)
  simp only [Functor.comp_map, Functor.comp_obj] at hn
  rw [← reassoc_of% hn]

end CategoryTheory.Endofunctor.IsoAlgebra
