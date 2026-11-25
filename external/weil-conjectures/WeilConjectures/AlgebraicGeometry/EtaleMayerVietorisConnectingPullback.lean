/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleOpenCohomologyMaps
import WeilConjectures.AlgebraicGeometry.EtaleMayerVietorisSectionDiagram

/-!
# Compatible connecting maps for the two étale Mayer–Vietoris sequences

Source: Stacks Project, Tag 0A50 and its proof.
(blueprint: lem-weil-pbc-etale-mayer-vietoris-connecting-pullback).
-/

@[expose] public section

universe u
open CategoryTheory AlgebraicGeometry
namespace AlgebraicGeometry.Etale

private theorem exact_transport
    {A : Type u} {B : Type u} {C : Type u}
    {A' : Type u} {B' : Type u} {C' : Type u}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [AddCommGroup A'] [AddCommGroup B'] [AddCommGroup C']
    (ea : A ≃+ A') (eb : B ≃+ B') (ec : C ≃+ C')
    {f : A → B} {g : B → C} {f' : A' → B'} {g' : B' → C'}
    (hf : ∀ x, eb (f x) = f' (ea x)) (hg : ∀ x, ec (g x) = g' (eb x))
    (hex : Function.Exact f g) : Function.Exact f' g' := by
  intro b
  constructor
  · intro hb
    have hz : g (eb.symm b) = 0 := by
      apply ec.injective
      simpa only [map_zero, hg, eb.apply_symm_apply] using hb
    obtain ⟨a, ha⟩ := (hex (eb.symm b)).mp hz
    refine ⟨ea a, ?_⟩
    rw [← hf, ha, eb.apply_symm_apply]
  · rintro ⟨a, rfl⟩
    obtain ⟨x, rfl⟩ := ea.surjective a
    rw [← hf, ← hg, (hex (f x)).mpr ⟨x, rfl⟩, map_zero]

private noncomputable def transportedBoundary
    (S : ShortComplex (CochainComplex AddCommGrpCat.{u} ℕ)) (hS : S.ShortExact)
    {A C : ℕ → Type u} [∀ q, AddCommGroup (A q)] [∀ q, AddCommGroup (C q)]
    (ea : ∀ q, S.X₁.homology q ≃+ A q) (ec : ∀ q, S.X₃.homology q ≃+ C q)
    (q : ℕ) : C q →+ A (q + 1) :=
  (ea (q + 1)).toAddMonoidHom.comp
    ((hS.δ q (q + 1) rfl).hom.comp (ec q).symm.toAddMonoidHom)

private theorem transportedBoundary_apply
    (S : ShortComplex (CochainComplex AddCommGrpCat.{u} ℕ)) (hS : S.ShortExact)
    {A C : ℕ → Type u} [∀ q, AddCommGroup (A q)] [∀ q, AddCommGroup (C q)]
    (ea : ∀ q, S.X₁.homology q ≃+ A q) (ec : ∀ q, S.X₃.homology q ≃+ C q)
    (q : ℕ) (x : S.X₃.homology q) :
    ea (q + 1) (hS.δ q (q + 1) rfl x) =
      transportedBoundary S hS ea ec q (ec q x) := by
  simp [transportedBoundary]

private theorem transport_sequence
    (S : ShortComplex (CochainComplex AddCommGrpCat.{u} ℕ)) (hS : S.ShortExact)
    {A B C : ℕ → Type u}
    [∀ q, AddCommGroup (A q)] [∀ q, AddCommGroup (B q)] [∀ q, AddCommGroup (C q)]
    (ea : ∀ q, S.X₁.homology q ≃+ A q) (eb : ∀ q, S.X₂.homology q ≃+ B q)
    (ec : ∀ q, S.X₃.homology q ≃+ C q)
    (r : ∀ q, A q → B q) (d : ∀ q, B q → C q)
    (hr : ∀ q x, eb q (HomologicalComplex.homologyMap S.f q x) = r q (ea q x))
    (hd : ∀ q x, ec q (HomologicalComplex.homologyMap S.g q x) = d q (eb q x)) :
    Function.Injective (r 0) ∧ ∀ q,
      Function.Exact (r q) (d q) ∧
      Function.Exact (d q) (transportedBoundary S hS ea ec q) ∧
      Function.Exact (transportedBoundary S hS ea ec q) (r (q + 1)) := by
  constructor
  · have := hS.mono_f
    have : Mono (HomologicalComplex.homologyMap S.f 0) :=
      HomologicalComplex.mono_homologyMap_of_mono_of_not_rel S.f 0 (by
        intro i
        change ¬ i + 1 = 0
        omega)
    have hi := (AddCommGrpCat.mono_iff_injective
      (HomologicalComplex.homologyMap S.f 0)).mp this
    intro x y hxy
    apply (ea 0).symm.injective
    apply hi
    apply (eb 0).injective
    simpa only [hr, AddEquiv.apply_symm_apply] using hxy
  · intro q
    refine ⟨?_, ?_, ?_⟩
    · exact exact_transport (ea q) (eb q) (ec q) (hr q) (hd q)
        ((ShortComplex.ab_exact_iff_function_exact _).mp (hS.homology_exact₂ q))
    · exact exact_transport (eb q) (ec q) (ea (q + 1)) (hd q)
        (transportedBoundary_apply S hS ea ec q)
        ((ShortComplex.ab_exact_iff_function_exact _).mp (hS.homology_exact₃ q (q + 1) rfl))
    · exact exact_transport (ec q) (ea (q + 1)) (eb (q + 1))
        (transportedBoundary_apply S hS ea ec q) (hr (q + 1))
        ((ShortComplex.ab_exact_iff_function_exact _).mp (hS.homology_exact₁ q (q + 1) rfl))

private theorem transport_boundary_naturality
    {SX SY : ShortComplex (CochainComplex AddCommGrpCat.{u} ℕ)} (φ : SX ⟶ SY)
    (hSX : SX.ShortExact) (hSY : SY.ShortExact)
    {AX CX AY CY : ℕ → Type u}
    [∀ q, AddCommGroup (AX q)] [∀ q, AddCommGroup (CX q)]
    [∀ q, AddCommGroup (AY q)] [∀ q, AddCommGroup (CY q)]
    (eaX : ∀ q, SX.X₁.homology q ≃+ AX q) (ecX : ∀ q, SX.X₃.homology q ≃+ CX q)
    (eaY : ∀ q, SY.X₁.homology q ≃+ AY q) (ecY : ∀ q, SY.X₃.homology q ≃+ CY q)
    (pa : ∀ q, AX q → AY q) (pc : ∀ q, CX q → CY q)
    (ha : ∀ q x, eaY q (HomologicalComplex.homologyMap φ.τ₁ q x) = pa q (eaX q x))
    (hc : ∀ q x, ecY q (HomologicalComplex.homologyMap φ.τ₃ q x) = pc q (ecX q x))
    (q : ℕ) (x : CX q) :
    transportedBoundary SY hSY eaY ecY q (pc q x) =
      pa (q + 1) (transportedBoundary SX hSX eaX ecX q x) := by
  obtain ⟨z, rfl⟩ := (ecX q).surjective x
  rw [← hc q z, ← transportedBoundary_apply SY hSY eaY ecY q]
  have hn : HomologicalComplex.homologyMap φ.τ₁ (q + 1) (hSX.δ q (q + 1) rfl z) =
      hSY.δ q (q + 1) rfl (HomologicalComplex.homologyMap φ.τ₃ q z) := by
    exact congrArg (fun f : SX.X₃.homology q ⟶ SY.X₁.homology (q + 1) ↦ f z)
      (HomologicalComplex.HomologySequence.δ_naturality φ hSX hSY q (q + 1) rfl)
  rw [← hn, ha, transportedBoundary_apply SX hSX eaX ecX q]

/-- There are exact Mayer–Vietoris sequences with pullback-compatible connecting maps.
Source: Stacks Project, Tag 0A50, construction in its proof; compatibility with pullback
is the explicit argument of steps 1–4 of the parent node.
(blueprint: lem-weil-pbc-etale-mayer-vietoris-connecting-pullback)

Proof: Choose nonnegative injective resolutions I of G and J of g⁻¹G. Exact inverse
image and the K-injectivity of J give a comparison β : g⁻¹I → J over the augmentations;
a homotopy from a complex in degree zero to J is zero in degree minus one, so this
comparison respects the augmentations exactly. For each W = X, U, V, U ∩ V, the unit
of inverse image followed by β gives a complex map I(W) → J(g⁻¹W). Naturality of both
maps makes the two restriction squares commute. Additivity preserves the difference
sign in the Mayer–Vietoris short exact sequences of complexes of sections. These
sequences are degreewise exact: the sheaf condition gives exactness at the first two
terms, and injectivity makes restriction from U to U ∩ V surjective, giving exactness
at the third term. The inverse-image opens cover Y since preimage preserves joins
and the top open; their intersection is g⁻¹(U ∩ V). Their homology sequences are exact, including
the initial degree-zero injection, and their
connecting maps commute with this morphism by δ_naturality. Restriction preserves
injectives; the restriction-to-sections identifications identify the horizontal maps
with cohomologyMap and openCohomologyRestriction. The unit-composition compatibility
identifies the vertical maps with cohomologyMap g and openCohomologyPullback. Transport
the homology sequences and their connecting maps along the Ext/derived-sections
comparison for Sheaf.H, computed on these same resolutions. Explicitly, Hom from
the constant integer sheaf is sections by evaluation at 1. An Ext cocycle pulls back
by the exact inverse-image functor and is precomposed with the constant-sheaf
comparison used in cohomologyMap. On its representing section this is the adjunction
unit; composing with β gives the section map above. On each open use the restricted
injective resolution and the identity lift of the coefficient comparison. Thus these
identifications intertwine the prescribed Ext pullbacks with the chain-level maps,
rather than using only existence of a coefficient-natural isomorphism. This gives
the two exact sequences and the last displayed square. Resolution independence makes these maps
independent of the comparison
choices. This statement does not assert the other two kinds of cohomology squares;
they follow separately from restriction naturality. When one open is empty or both
opens are all of X, this is the split sequence with zero connecting maps; for g the
identity choose the same resolution on both sides. -/
theorem etale_mayerVietoris_connecting_pullback
    {X Y : Scheme.{u}} (g : Y ⟶ X)
    (U V : X.Opens) (hcover : U ⊔ V = ⊤)
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    ∃ δX : ∀ q : ℕ, Sheaf.H ((upperStar AddCommGrpCat.{u + 1} ((U ⊓ V).ι)).obj G) q →+ Sheaf.H G
        (q + 1),
    ∃ δY : ∀ q : ℕ, Sheaf.H ((upperStar AddCommGrpCat.{u + 1} ((g ⁻¹ᵁ (U ⊓ V)).ι)).obj ((upperStar
        AddCommGrpCat.{u + 1} (g)).obj G)) q →+ Sheaf.H ((upperStar AddCommGrpCat.{u + 1} (g)).obj
        G) (q + 1),
    Function.Injective (fun x : Sheaf.H G 0 => ((cohomologyMap U.ι G) 0 x, (cohomologyMap V.ι G) 0
        x)) ∧
    (∀ q : ℕ, Function.Exact (fun x : Sheaf.H G q => ((cohomologyMap U.ι G) q x, (cohomologyMap V.ι
        G) q x))
        (fun x : Sheaf.H ((upperStar AddCommGrpCat.{u + 1} (U.ι)).obj G) q × Sheaf.H ((upperStar
        AddCommGrpCat.{u + 1} (V.ι)).obj G) q =>
          (openCohomologyRestriction (inf_le_left : U ⊓ V ≤ U) G) q x.1 - (openCohomologyRestriction
        (inf_le_right : U ⊓ V ≤ V) G) q x.2) ∧
      Function.Exact (fun x : Sheaf.H ((upperStar AddCommGrpCat.{u + 1} (U.ι)).obj G) q × Sheaf.H
        ((upperStar AddCommGrpCat.{u + 1} (V.ι)).obj G) q =>
          (openCohomologyRestriction (inf_le_left : U ⊓ V ≤ U) G) q x.1 - (openCohomologyRestriction
        (inf_le_right : U ⊓ V ≤ V) G) q x.2) (δX q) ∧
      Function.Exact (δX q)
        (fun x => ((cohomologyMap U.ι G) (q + 1) x, (cohomologyMap V.ι G) (q + 1) x))) ∧
    Function.Injective (fun x : Sheaf.H ((upperStar AddCommGrpCat.{u + 1} (g)).obj G) 0 =>
        ((cohomologyMap (g ⁻¹ᵁ U).ι ((upperStar AddCommGrpCat.{u + 1} g).obj G)) 0
        x, (cohomologyMap (g ⁻¹ᵁ V).ι ((upperStar AddCommGrpCat.{u + 1} g).obj G)) 0 x)) ∧
    (∀ q : ℕ, Function.Exact (fun x : Sheaf.H ((upperStar AddCommGrpCat.{u + 1} (g)).obj G) q =>
        ((cohomologyMap (g ⁻¹ᵁ U).ι ((upperStar AddCommGrpCat.{u + 1} g).obj G)) q x, (cohomologyMap
        (g ⁻¹ᵁ V).ι ((upperStar AddCommGrpCat.{u + 1} g).obj G)) q x))
        (fun x : Sheaf.H ((upperStar AddCommGrpCat.{u + 1} ((g ⁻¹ᵁ U).ι)).obj ((upperStar
        AddCommGrpCat.{u + 1} (g)).obj G)) q × Sheaf.H ((upperStar AddCommGrpCat.{u + 1} ((g ⁻¹ᵁ
        V).ι)).obj ((upperStar AddCommGrpCat.{u + 1} (g)).obj G)) q =>
          (openCohomologyRestriction (g.preimage_mono (inf_le_left : U ⊓ V ≤ U))
          ((upperStar AddCommGrpCat.{u + 1} g).obj G)) q x.1 - (openCohomologyRestriction
        (g.preimage_mono (inf_le_right : U ⊓ V ≤ V))
          ((upperStar AddCommGrpCat.{u + 1} g).obj G)) q x.2) ∧
      Function.Exact (fun x : Sheaf.H ((upperStar AddCommGrpCat.{u + 1} ((g ⁻¹ᵁ U).ι)).obj
        ((upperStar AddCommGrpCat.{u + 1} (g)).obj G)) q × Sheaf.H ((upperStar AddCommGrpCat.{u +
        1} ((g ⁻¹ᵁ V).ι)).obj ((upperStar AddCommGrpCat.{u + 1} (g)).obj G)) q =>
          (openCohomologyRestriction (g.preimage_mono (inf_le_left : U ⊓ V ≤ U))
          ((upperStar AddCommGrpCat.{u + 1} g).obj G)) q x.1 - (openCohomologyRestriction
        (g.preimage_mono (inf_le_right : U ⊓ V ≤ V))
          ((upperStar AddCommGrpCat.{u + 1} g).obj G)) q x.2) (δY q) ∧
      Function.Exact (δY q)
        (fun x => ((cohomologyMap (g ⁻¹ᵁ U).ι ((upperStar AddCommGrpCat.{u + 1} g).obj G)) (q + 1)
        x, (cohomologyMap (g ⁻¹ᵁ V).ι ((upperStar AddCommGrpCat.{u + 1} g).obj G)) (q + 1) x))) ∧
    (∀ q : ℕ, ∀ x : Sheaf.H ((upperStar AddCommGrpCat.{u + 1} ((U ⊓ V).ι)).obj G) q,
      δY q ((openCohomologyPullback g (U ⊓ V) G) q x) = cohomologyMap g G (q + 1) (δX q x)) := by
  obtain ⟨SX, SY, φ, hSX, hSY, eAX, eBX, eCX, eAY, eBY, eCY,
    hrX, hdX, hrY, hdY, hpA, hpC⟩ :=
    etale_mayerVietoris_section_diagram g U V hcover G
  refine ⟨transportedBoundary SX hSX eAX eCX,
    transportedBoundary SY hSY eAY eCY, ?_⟩
  obtain ⟨hX0, hX⟩ := transport_sequence SX hSX eAX eBX eCX
    (fun q x ↦ (cohomologyMap U.ι G q x, cohomologyMap V.ι G q x))
    (fun q x ↦ openCohomologyRestriction (inf_le_left : U ⊓ V ≤ U) G q x.1 -
      openCohomologyRestriction (inf_le_right : U ⊓ V ≤ V) G q x.2) hrX hdX
  obtain ⟨hY0, hY⟩ := transport_sequence SY hSY eAY eBY eCY
    (fun q x ↦
      (cohomologyMap (g ⁻¹ᵁ U).ι ((upperStar AddCommGrpCat.{u + 1} g).obj G) q x,
       cohomologyMap (g ⁻¹ᵁ V).ι ((upperStar AddCommGrpCat.{u + 1} g).obj G) q x))
    (fun q x ↦
      openCohomologyRestriction (g.preimage_mono (inf_le_left : U ⊓ V ≤ U))
        ((upperStar AddCommGrpCat.{u + 1} g).obj G) q x.1 -
      openCohomologyRestriction (g.preimage_mono (inf_le_right : U ⊓ V ≤ V))
        ((upperStar AddCommGrpCat.{u + 1} g).obj G) q x.2) hrY hdY
  exact ⟨hX0, hX, hY0, hY,
    transport_boundary_naturality φ hSX hSY eAX eCX eAY eCY
      (fun q ↦ cohomologyMap g G q) (fun q ↦ openCohomologyPullback g (U ⊓ V) G q)
      hpA hpC⟩

end AlgebraicGeometry.Etale
