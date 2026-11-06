import Mathlib
import Langlands.AlgebraicGeometry.ProperOfFibres.Approximation
import Langlands.AlgebraicGeometry.ProperOfFibres.NoetherianCore
import Langlands.AlgebraicGeometry.Morphisms.FpqcFiniteDescent
import Langlands.AlgebraicGeometry.GeometricallyConnectedDescent

/-! # Properness over a normal local domain from the two fibres -/

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.ProperOfFibres

/-- A field extension is surjective, flat and quasi-compact on spectra. -/
theorem surjective_flat_quasiCompact_SpecMap {K L : Type u} [Field K] [Field L] (φ : K →+* L) :
    (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u})
      (Spec.map (CommRingCat.ofHom φ)) := by
  have h : (CommRingCat.ofHom φ).hom.FaithfullyFlat := by
    algebraize [φ]
    change Module.FaithfullyFlat K L
    infer_instance
  obtain ⟨h₁, h₂⟩ := (flat_and_surjective_SpecMap_iff _).mpr h
  exact ⟨⟨h₂, h₁⟩, inferInstance⟩

/-- Base change along a factorization of the bottom map, in existential form. -/
theorem exists_isPullback_of_fac {X X₁ Y B B' : Scheme.{u}} {π : X ⟶ X₁} {g : X ⟶ Y}
    {f : X₁ ⟶ B} {ι : Y ⟶ B} (sq : IsPullback π g f ι) (κ : B' ⟶ B) (ι' : Y ⟶ B')
    (hι : ι' ≫ κ = ι) : ∃ e : X ⟶ pullback f κ, IsPullback e g (pullback.snd f κ) ι' :=
  ⟨_, isPullback_lift_of_fac sq κ ι' hι (by rw [Category.assoc, hι]; exact sq.w)⟩

/-- Let `X ⟶ Spec V` be the base change of `X₀ ⟶ Spec N` along `α : N ⟶ V`, and let
`β : N ⟶ B`, `γ : B ⟶ F`, `δ : V ⟶ E` and `ε : F ⟶ E` be ring maps with
`δ ∘ α = ε ∘ γ ∘ β`. Then the base change of `X` along `δ` is the base change of
`(X₀ ×_N B) ×_B F` along `ε`. -/
theorem exists_isPullback_fibre {N B F V E : Type u} [CommRing N] [CommRing B] [CommRing F]
    [CommRing V] [CommRing E] {X X₀ : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of V)}
    {f₀ : X₀ ⟶ Spec (CommRingCat.of N)} {π : X ⟶ X₀} {α : N →+* V}
    (sq : IsPullback π f f₀ (Spec.map (CommRingCat.ofHom α))) (β : N →+* B) (γ : B →+* F)
    (δ : V →+* E) (ε : F →+* E) (h : δ.comp α = (ε.comp γ).comp β) :
    ∃ e, IsPullback e (pullback.snd f (Spec.map (CommRingCat.ofHom δ)))
      (pullback.snd (pullback.snd f₀ (Spec.map (CommRingCat.ofHom β)))
        (Spec.map (CommRingCat.ofHom γ))) (Spec.map (CommRingCat.ofHom ε)) := by
  have sq₁ := (IsPullback.of_hasPullback f (Spec.map (CommRingCat.ofHom δ))).paste_horiz sq
  have hι : (Spec.map (CommRingCat.ofHom ε) ≫ Spec.map (CommRingCat.ofHom γ)) ≫
      Spec.map (CommRingCat.ofHom β) =
        Spec.map (CommRingCat.ofHom δ) ≫ Spec.map (CommRingCat.ofHom α) := by
    simp only [← Spec.map_comp, ← CommRingCat.ofHom_comp, h]
  obtain ⟨e₁, sq₂⟩ := exists_isPullback_of_fac sq₁ _ _ hι
  exact exists_isPullback_of_fac sq₂ _ _ rfl

/-- The lift to `V` of a ring map from a localization at the preimage of the maximal ideal is
injective and local. -/
theorem lift_injective_isLocalHom {V : Type u} [CommRing V] [IsLocalRing V] {N : Type u}
    [CommRing N] [IsDomain N] (φ : N →+* V) (hφ : Function.Injective φ) (B : Type u)
    [CommRing B] [Algebra N B]
    [IsLocalization.AtPrime B ((IsLocalRing.maximalIdeal V).comap φ)]
    (hunit : ∀ y : ((IsLocalRing.maximalIdeal V).comap φ).primeCompl, IsUnit (φ y)) :
    Function.Injective (IsLocalization.lift hunit : B →+* V) ∧
      IsLocalHom (IsLocalization.lift hunit : B →+* V) := by
  set p := (IsLocalRing.maximalIdeal V).comap φ
  have hle : p.primeCompl ≤ nonZeroDivisors N :=
    le_nonZeroDivisors_of_noZeroDivisors fun h => h (Submodule.zero_mem _)
  refine ⟨?_, ⟨fun b hb => ?_⟩⟩
  · rw [IsLocalization.lift_injective_iff]
    intro x y
    rw [(IsLocalization.injective B hle).eq_iff, hφ.eq_iff]
  · obtain ⟨n, s, rfl⟩ := IsLocalization.exists_mk'_eq p.primeCompl b
    have hspec := congrArg (IsLocalization.lift hunit : B →+* V)
      (IsLocalization.mk'_spec B n s)
    rw [map_mul, IsLocalization.lift_eq, IsLocalization.lift_eq] at hspec
    have hn : IsUnit (φ n) := hspec ▸ hb.mul (hunit s)
    have hn' : n ∈ p.primeCompl := fun h => (IsLocalRing.mem_maximalIdeal _).mp h hn
    have hu : IsUnit (IsLocalization.mk' B n s * algebraMap N B s) := by
      rw [IsLocalization.mk'_spec]
      exact IsLocalization.map_units B ⟨n, hn'⟩
    exact isUnit_of_mul_isUnit_left hu

section

variable {V : Type u} [CommRing V] [IsLocalRing V] [IsDomain V] [IsIntegrallyClosed V]
  (K : Type u) [Field K] [Algebra V K] [IsFractionRing V K]

/-- **Properness over a normal local domain from its two fibres.** Let `V` be an integrally
closed local domain with fraction field `K`. Let `f : X ⟶ Spec V` be smooth and quasi-compact,
and let `j : X ⟶ Y` be a monomorphism over `Spec V` into a proper `V`-scheme of finite
presentation. If the generic fibre of `f` is proper and geometrically connected and the closed
fibre of `f` is proper and nonempty, then `f` is proper. -/
theorem isProper_of_isLocalRing {X Y : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of V)) [Smooth f]
    [QuasiCompact f] (g : Y ⟶ Spec (CommRingCat.of V)) [IsProper g]
    [LocallyOfFinitePresentation g] (j : X ⟶ Y) [Mono j] (hfac : j ≫ g = f)
    [IsProper (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap V K))))]
    [GeometricallyConnected (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap V K))))]
    [IsProper (pullback.snd f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue V))))]
    [Nonempty ↥(pullback f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue V))))] :
    IsProper f := by
  obtain ⟨N, hN, hNi, M, hM₁, hM₂, hM₃⟩ := exists_normal_model f g j hfac
  have : Algebra.FiniteType ℤ N := (Subalgebra.fg_iff_finiteType N).mp hN
  let φ : N →+* V := algebraMap N V
  have hφ : Function.Injective φ := Subtype.val_injective
  let p : Ideal N := (IsLocalRing.maximalIdeal V).comap φ
  have : p.IsPrime := Ideal.comap_isPrime _ _
  obtain ⟨B, _, _, _⟩ : ∃ (B : Type u) (_ : CommRing B) (_ : Algebra N B),
      IsLocalization.AtPrime B p := ⟨Localization.AtPrime p, _, _, inferInstance⟩
  have : IsDomain B :=
    IsLocalization.isDomain_of_le_nonZeroDivisors B p.primeCompl_le_nonZeroDivisors
  have : IsLocalRing B := IsLocalization.AtPrime.isLocalRing B p
  have hunit : ∀ y : p.primeCompl, IsUnit (φ y) := fun y =>
    of_not_not fun h => y.2 ((IsLocalRing.mem_maximalIdeal _).mpr h)
  let ψ : B →+* V := IsLocalization.lift hunit
  have hψ : ψ.comp (algebraMap N B) = φ := IsLocalization.lift_comp hunit
  obtain ⟨hψinj, hψloc⟩ := lift_injective_isLocalHom φ hφ B hunit
  have hinj : Function.Injective ((algebraMap V K).comp ψ) :=
    (IsFractionRing.injective V K).comp hψinj
  let ε : (FractionRing B) →+* K := IsFractionRing.lift (K := (FractionRing B)) hinj
  have hε : ε.comp (algebraMap B (FractionRing B)) = (algebraMap V K).comp ψ :=
    RingHom.ext fun x => IsFractionRing.lift_algebraMap (K := (FractionRing B)) hinj x
  -- the generic fibre
  obtain ⟨e₁, sq₁⟩ := exists_isPullback_fibre M.MX.isPullback (algebraMap N B)
    (algebraMap B (FractionRing B)) (algebraMap V K) ε (by rw [hε, RingHom.comp_assoc, hψ])
  have hQ₁ := surjective_flat_quasiCompact_SpecMap ε
  have : IsProper (pullback.snd (pullback.snd M.MX.f₀ (Spec.map (CommRingCat.ofHom
      (algebraMap N B)))) (Spec.map (CommRingCat.ofHom (algebraMap B (FractionRing B))))) :=
    MorphismProperty.of_isPullback_of_descendsAlong (P := @IsProper) sq₁.flip hQ₁ ‹_›
  have : Surjective (Spec.map (CommRingCat.ofHom ε)) := hQ₁.1.1
  have : GeometricallyConnected (pullback.snd (pullback.snd M.MX.f₀ (Spec.map
      (CommRingCat.ofHom (algebraMap N B))))
      (Spec.map (CommRingCat.ofHom (algebraMap B (FractionRing B))))) :=
    geometricallyConnected_of_surjective_isPullback _ _ sq₁
  -- the closed fibre
  let ρ := IsLocalRing.ResidueField.map ψ
  obtain ⟨e₂, sq₂⟩ := exists_isPullback_fibre M.MX.isPullback (algebraMap N B)
    (IsLocalRing.residue B) (IsLocalRing.residue V) ρ
    (by rw [IsLocalRing.ResidueField.map_comp_residue, RingHom.comp_assoc, hψ])
  have : IsProper (pullback.snd (pullback.snd M.MX.f₀ (Spec.map (CommRingCat.ofHom
      (algebraMap N B)))) (Spec.map (CommRingCat.ofHom (IsLocalRing.residue B)))) :=
    MorphismProperty.of_isPullback_of_descendsAlong (P := @IsProper) sq₂.flip
      (surjective_flat_quasiCompact_SpecMap ρ) ‹_›
  have : Nonempty ↥(pullback (pullback.snd M.MX.f₀ (Spec.map (CommRingCat.ofHom
      (algebraMap N B)))) (Spec.map (CommRingCat.ofHom (IsLocalRing.residue B)))) :=
    ⟨e₂ (Classical.arbitrary _)⟩
  have hB : IsProper (pullback.snd M.MX.f₀ (Spec.map (CommRingCat.ofHom (algebraMap N B)))) :=
    isProper_pullback_snd_of_mono p B (FractionRing B) M.MX.f₀ M.MY.f₀ M.j₀ M.fac
  -- descend from `B` to `V`
  obtain ⟨e₃, sq₃⟩ := exists_isPullback_of_fac M.MX.isPullback
    (Spec.map (CommRingCat.ofHom (algebraMap N B))) (Spec.map (CommRingCat.ofHom ψ))
    (by rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hψ])
  exact MorphismProperty.of_isPullback (P := @IsProper) sq₃ hB

end

end Langlands.AlgebraicGeometry.ProperOfFibres
