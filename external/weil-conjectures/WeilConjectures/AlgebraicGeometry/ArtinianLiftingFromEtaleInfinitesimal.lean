/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.HopkinsLevitzki
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import WeilConjectures.AlgebraicGeometry.FlatUnramifiedFormallyEtale
public import Mathlib.RingTheory.Noetherian.Nilpotent

/-! # Artinian test-diagram lifting from infinitesimal étaleness

Source: Stacks Project, Tag 0A43, proof of part (1).
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- A proper length-one ideal in a local ring is annihilated by the maximal ideal.
In particular, the kernel below has square zero. Source: Stacks 0A43, the small
extension in its proof, and the simple-module characterization of length one. -/
private theorem kernel_sq_zero {R B : Type*} [CommRing R] [CommRing B]
    [IsLocalRing R] [Nontrivial B] (φ : R →+* B)
    (h : Module.length R ↥(RingHom.ker φ) = 1) : RingHom.ker φ ^ 2 = ⊥ := by
  have : IsSimpleModule R ↥(RingHom.ker φ) := Module.length_eq_one_iff.mp h
  have hann : Module.annihilator R ↥(RingHom.ker φ) = IsLocalRing.maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal (IsSimpleModule.annihilator_isMaximal)
  apply le_antisymm _ bot_le
  rw [pow_two]
  apply Ideal.mul_le.mpr
  intro a ha b hb
  have ha' : a ∈ Module.annihilator R ↥(RingHom.ker φ) := by
    rw [hann]
    exact IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top φ) ha
  have hz := Module.mem_annihilator.mp ha' (⟨b, hb⟩ : RingHom.ker φ)
  simpa using congrArg Subtype.val hz

/-- The square-zero ring kernel gives a square-zero defining ideal sheaf on Spec.
Source: Stacks 04EX, first-order thickenings; naturality of the global sections
isomorphisms identifies the two kernels. -/
private theorem spec_first_order {R B : Type u} [CommRing R] [CommRing B]
    [IsLocalRing R] [Nontrivial B] (φ : R →+* B) (hs : Function.Surjective φ)
    (h : Module.length R ↥(RingHom.ker φ) = 1) :
    IsFirstOrderThickening (Spec.map (CommRingCat.ofHom φ)) := by
  refine ⟨IsClosedImmersion.spec_of_surjective _ hs, ?_⟩
  apply Scheme.IdealSheafData.ext_of_isAffine
  simp only [Scheme.IdealSheafData.ideal_pow, Pi.pow_apply,
    Scheme.Hom.ker_apply, Scheme.IdealSheafData.ideal_bot]
  have hn := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ)
  have he : (Spec.map (CommRingCat.ofHom φ)).appTop =
      (Scheme.ΓSpecIso (.of R)).hom ≫ CommRingCat.ofHom φ ≫
        (Scheme.ΓSpecIso (.of B)).inv := by
    rw [← Category.assoc, ← hn, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  change RingHom.ker (Spec.map (CommRingCat.ofHom φ)).appTop.hom ^ 2 = ⊥
  rw [he]
  simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom]
  rw [← RingHom.comap_ker]
  change (RingHom.ker
    (((Scheme.ΓSpecIso (.of B)).symm.commRingCatIsoToRingEquiv.toRingHom).comp φ)).comap
      (Scheme.ΓSpecIso (.of R)).hom.hom ^ 2 = ⊥
  rw [RingHom.ker_equiv_comp]
  apply le_antisymm _ bot_le
  refine (Ideal.le_comap_pow _ 2).trans ?_
  rw [kernel_sq_zero φ h, Ideal.comap_bot_of_injective]
  exact (Scheme.ΓSpecIso (.of R)).commRingCatIsoToRingEquiv.injective

/-- An Artinian local test map whose closed point lies in the support of an ideal
factors through a positive power of that ideal. Source: Stacks 0A43, proof of (1).
Pull back the ideal to the test scheme; its support is the whole space, so its
ideal of global sections lies in the nilradical. Noetherianity makes this ideal
nilpotent. Pullback commutes with powers, and the resulting closed immersion
with zero kernel is an isomorphism, giving the factorization. -/
private theorem artinian_factor {S : Scheme.{u}} (J : S.IdealSheafData)
    (R : Type u) [CommRing R] [IsArtinianRing R] [IsLocalRing R]
    (β : Spec (.of R) ⟶ S) (hx : β (IsLocalRing.closedPoint R) ∈ J.support) :
    ∃ (n : ℕ) (βn : Spec (.of R) ⟶ (J ^ (n + 1)).subscheme),
      βn ≫ (J ^ (n + 1)).subschemeι = β := by
  let W := Spec (CommRingCat.of R)
  let I := J.comap β
  have hsupport : I.support = ⊤ := by
    ext y
    rw [show I = J.comap β from rfl, Scheme.IdealSheafData.support_comap]
    change β y ∈ J.support ↔ True
    apply iff_true_intro
    have hy : y = IsLocalRing.closedPoint R := by
      apply PrimeSpectrum.ext
      exact IsLocalRing.eq_maximalIdeal (IsArtinianRing.isMaximal_of_isPrime _)
    simpa only [hy] using hx
  have : IsNoetherianRing Γ(W, ⊤) :=
    isNoetherianRing_of_ringEquiv R (Scheme.ΓSpecIso (.of R)).commRingCatIsoToRingEquiv.symm
  let U : W.affineOpens := ⟨⊤, isAffineOpen_top W⟩
  let K := I.ideal U
  have hK : K ≤ nilradical Γ(W, ⊤) := by
    apply (PrimeSpectrum.zeroLocus_eq_univ_iff (K : Set Γ(W, ⊤))).mp
    apply Set.eq_univ_of_forall
    intro p
    rw [← (isAffineOpen_top W).fromSpec_preimage_zeroLocus]
    exact (Scheme.IdealSheafData.mem_support_iff_of_mem (I := I)
      (U := U) (by trivial)).mp (by rw [hsupport]; trivial)
  obtain ⟨n, hn⟩ := (Ideal.FG.isNilpotent_iff_le_nilradical
    (IsNoetherian.noetherian K)).mpr hK
  have hI : I ^ (n + 1) = ⊥ := by
    apply Scheme.IdealSheafData.ext_of_isAffine
    change K ^ (n + 1) = ⊥
    rw [pow_succ, hn, zero_mul]
    rfl
  have hz : (pullback.fst β (J ^ (n + 1)).subschemeι).ker = ⊥ := by
    change (J ^ (n + 1)).comap β = ⊥
    rw [Scheme.IdealSheafData.comap_pow]
    exact hI
  have : IsIso (pullback.fst β (J ^ (n + 1)).subschemeι) :=
    IsClosedImmersion.isIso_iff_ker_eq_bot.mpr hz
  refine ⟨n, inv (pullback.fst β (J ^ (n + 1)).subschemeι) ≫
    pullback.snd β (J ^ (n + 1)).subschemeι, ?_⟩
  rw [Category.assoc, ← pullback.condition, ← Category.assoc,
    IsIso.inv_hom_id, Category.id_comp]

/-- Every small Artinian test diagram at a point over the closed subscheme lifts.
Source: Stacks Project, More on Morphisms, Lemma 0A43, proof of part (1).
(blueprint: lem-weil-pbc-etale-infinitesimal-artinian-tests)

Proof: The Artinian local spectra have a single point. The test square puts
β's closed point in the support of J. Pull back J to Spec B'; this ideal sheaf
has full support. Its global sections form an ideal in a Noetherian ring and
lie in the nilradical, so some positive power vanishes. Pullback commutes with
powers. The pullback projection along J^(n+1) is therefore a closed immersion
with zero kernel and hence an isomorphism; its inverse gives β's factorization
through Z_n. The test square then gives α's factorization through X_n.
The length-one kernel of φ is a simple module. Its annihilator is the local
ring's maximal ideal, which contains the proper kernel; hence the kernel has
square zero. Naturality of Γ(Spec R) ≅ R gives the corresponding first-order
thickening of affine schemes. Etaleness of X_n → Z_n supplies flatness and an
open immersion diagonal. Apply the formal smoothness half of
flat_unramified_formally_etale to lift to X_n, and compose with X_n → X.
The pullback projection equations give both required equalities. -/
theorem artinian_lifting_tests_of_etale_infinitesimal
    {X S Z : Scheme.{u}} (g : X ⟶ S) (i : Z ⟶ S)
    [IsClosedImmersion i] (J : S.IdealSheafData) (hJ : J = i.ker)
    (h_etale : ∀ n : ℕ,
      Etale (pullback.snd g ((J ^ (n + 1)).subschemeι)))
    (x : X) (hx : (g : X → S) x ∈ Set.range (i : Z → S)) :
    ∀ (B' B : Type u) [CommRing B'] [CommRing B]
      [IsArtinianRing B'] [IsArtinianRing B] [IsLocalRing B'] [IsLocalRing B]
      (φ : B' →+* B),
      Function.Surjective φ → Module.length B' ↥(RingHom.ker φ) = 1 →
      ∀ (α : Spec (CommRingCat.of B) ⟶ X) (β : Spec (CommRingCat.of B') ⟶ S),
        α ≫ g = Spec.map (CommRingCat.ofHom φ) ≫ β →
        α (IsLocalRing.closedPoint B) = x →
        ∃ γ : Spec (CommRingCat.of B') ⟶ X,
          Spec.map (CommRingCat.ofHom φ) ≫ γ = α ∧ γ ≫ g = β := by
  intro B' B _ _ _ _ _ _ φ hsurj hlength α β hcomm hα
  have hp : Spec.map (CommRingCat.ofHom φ) (IsLocalRing.closedPoint B) =
      IsLocalRing.closedPoint B' := by
    apply PrimeSpectrum.ext
    exact IsLocalRing.eq_maximalIdeal (IsArtinianRing.isMaximal_of_isPrime _)
  have hβ : β (IsLocalRing.closedPoint B') = g x := by
    have he := congrArg (fun f : Spec (.of B) ⟶ S ↦ f (IsLocalRing.closedPoint B)) hcomm
    simpa only [Scheme.Hom.comp_apply, hp, hα] using he.symm
  have hxJ : β (IsLocalRing.closedPoint B') ∈ J.support := by
    rw [hβ, hJ]
    exact i.range_subset_ker_support hx
  obtain ⟨n, βn, hβn⟩ := artinian_factor J B' β hxJ
  let j := (J ^ (n + 1)).subschemeι
  let αn : Spec (.of B) ⟶ pullback g j :=
    pullback.lift α (Spec.map (CommRingCat.ofHom φ) ≫ βn) (by
      rw [Category.assoc, hβn]
      exact hcomm)
  have : Etale (pullback.snd g j) := h_etale n
  let : (Spec (.of B')).Over (J ^ (n + 1)).subscheme := ⟨βn⟩
  have hform : FormallySmooth (pullback.snd g j) :=
    (flat_unramified_formally_etale (pullback.snd g j)
      ⟨inferInstance, inferInstance⟩).2
  obtain ⟨γn, hγn, hγbase⟩ := hform (Spec.map (CommRingCat.ofHom φ))
    (spec_first_order φ hsurj hlength) αn (by
      change αn ≫ pullback.snd g j = Spec.map (CommRingCat.ofHom φ) ≫ βn
      exact pullback.lift_snd _ _ _)
  refine ⟨γn ≫ pullback.fst g j, ?_, ?_⟩
  · rw [← Category.assoc, hγn]
    exact pullback.lift_fst _ _ _
  · rw [Category.assoc, pullback.condition, ← Category.assoc, hγbase]
    exact hβn

end AlgebraicGeometry
