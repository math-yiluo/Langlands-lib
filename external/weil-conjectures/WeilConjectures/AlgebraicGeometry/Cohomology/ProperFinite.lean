/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.ProperFinite.ChowStep

/-!
# Finiteness of the cohomology of coherent sheaves on proper schemes

Let `A` be a noetherian ring and `X` a proper scheme over `Spec A`. For every coherent
`𝒪_X`-module `𝒢`, the cohomology groups `H^q(X, 𝒢)` are finite `A`-modules
(`AlgebraicGeometry.Scheme.Modules.hasFiniteH_of_isProper`) [Stacks, Tag 02O6],
[EGA III₁, 3.2.1].

The proof is by noetherian induction on the open subsets `U` of `X`, for the statement "every
coherent module vanishing on `U` has finite cohomology". A coherent module `𝒢` vanishing on `U`
is the pushforward of a coherent module `𝒢'` on a closed subscheme `i : Z ⟶ X` disjoint from `U`
(`AlgebraicGeometry.Scheme.Modules.exists_isIso_pullbackUnit_subschemeι`), and `i` being affine,
`𝒢` and `𝒢'` have the same cohomology. If `Z` is nonempty, the Chow step
(`AlgebraicGeometry.Scheme.Modules.exists_hasFiniteH_hom_isIso_restrict`) gives a morphism
`𝒢' ⟶ 𝒢''` to a coherent module with finite cohomology which is an isomorphism over a
nonempty open `W` of `Z`. Its kernel and cokernel are pushed forward to coherent modules on `X`
vanishing on the strictly larger open `U ∪ (X \ i(Z \ W))`, which have finite cohomology by
induction; hence so has `𝒢'`.
-/

@[expose] public section

universe u

open CategoryTheory Limits TopologicalSpace

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {A : Type u} [CommRing A]

/-- A zero module has finite cohomology. -/
lemma HasFiniteH.of_isZero {X : Scheme.{u}} {p : X ⟶ Spec (.of A)} {M : X.Modules}
    (h : IsZero M) : HasFiniteH p M := fun q ↦ by
  let := moduleHOfSpec p M q
  have := subsingleton_H_of_isZero h q
  infer_instance

variable [IsNoetherianRing A]

/-- **Finiteness of coherent cohomology on proper schemes over a noetherian ring.** Let `A` be
noetherian, `p : X ⟶ Spec A` proper and `𝒢` a coherent `𝒪_X`-module. Then every `H^q(X, 𝒢)`
is a finite `A`-module [Stacks, Tag 02O6], [EGA III₁, 3.2.1].

(blueprint: `lem-pc-coherent-hi`) -/
theorem hasFiniteH_of_isProper {X : Scheme.{u}} (p : X ⟶ Spec (.of A)) [IsProper p]
    (G : X.Modules) [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) G]
    [SheafOfModules.IsFinitePresentation (R := X.ringCatSheaf) G] : HasFiniteH p G := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  have : IsNoetherian X := {}
  suffices H : ∀ (U : X.Opens) (G : X.Modules)
      [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) G]
      [SheafOfModules.IsFinitePresentation (R := X.ringCatSheaf) G],
      IsZero (G.restrict U.ι) → HasFiniteH p G by
    have : IsEmpty (⊥ : X.Opens).toScheme := ⟨fun x ↦ x.2⟩
    exact H ⊥ G (isZero_of_isEmpty _)
  intro U
  induction U using WellFoundedGT.induction with
  | _ U ih =>
  intro G _ _ hG
  obtain ⟨I, hIU, hiso⟩ := exists_isIso_pullbackUnit_subschemeι G U hG
  let i := I.subschemeι
  let G' := (pullback i).obj G
  refine HasFiniteH.of_iso (asIso (pullbackUnit i G)).symm
    ((hasFiniteH_pushforward_iff i p G').2 ?_)
  rcases isEmpty_or_nonempty I.subscheme with hZ | hZ
  · exact HasFiniteH.of_isZero (isZero_of_isEmpty _)
  have : IsLocallyNoetherian I.subscheme := LocallyOfFiniteType.isLocallyNoetherian (i ≫ p)
  obtain ⟨G'', _, _, φ, W, hW, hφ, hG''⟩ := exists_hasFiniteH_hom_isIso_restrict (i ≫ p) G'
  -- the open `X \ i(Z \ W)`
  let W' : X.Opens := ⟨(i.base '' (W : Set I.subscheme)ᶜ)ᶜ,
    (i.isClosedEmbedding.isClosedMap _ W.isOpen.isClosed_compl).isOpen_compl⟩
  have hsupp (z : I.subscheme) : i.base z ∉ U := fun h ↦ hIU _ h
    (show i.base z ∈ (I.support : Set X) from I.range_subschemeι ▸ ⟨z, rfl⟩)
  have hpre : i ⁻¹ᵁ (U ⊔ W') ≤ W := by
    intro z hz
    obtain hz | hz := hz
    · exact (hsupp z hz).elim
    · by_contra hzW
      exact hz ⟨z, hzW, rfl⟩
  have hlt : U < U ⊔ W' := by
    obtain ⟨z, hz⟩ := hW
    refine lt_of_le_of_ne le_sup_left fun h ↦ hsupp z ?_
    rw [h]
    refine Or.inr fun ⟨z', hz', hzz'⟩ ↦ hz' ?_
    rwa [i.isClosedEmbedding.injective hzz']
  have key (M : I.subscheme.Modules)
      [SheafOfModules.IsQuasicoherent (R := I.subscheme.ringCatSheaf) M]
      [SheafOfModules.IsFinitePresentation (R := I.subscheme.ringCatSheaf) M]
      (hM : IsZero (M.restrict W.ι)) : HasFiniteH (i ≫ p) M := by
    have := isQuasicoherent_pushforward_of_isClosedImmersion i M
    have := isFinitePresentation_pushforward_of_isClosedImmersion i M
    refine (hasFiniteH_pushforward_iff i p M).1 (ih _ hlt _ ?_)
    rw [isZero_restrict_iff] at hM ⊢
    intro V hV
    exact hM _ ((i.preimage_mono hV).trans hpre)
  have := hφ
  have := isQuasicoherent_kernel φ
  have := isFinitePresentation_kernel φ
  have := isQuasicoherent_cokernel φ
  have := isFinitePresentation_cokernel φ
  exact HasFiniteH.of_hom φ (key _ (isZero_restrict_kernel_of_isIso φ W))
    (key _ (isZero_restrict_cokernel_of_isIso φ W)) hG''

end AlgebraicGeometry.Scheme.Modules
