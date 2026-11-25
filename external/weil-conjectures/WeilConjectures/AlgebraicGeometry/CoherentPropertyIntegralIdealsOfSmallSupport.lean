/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.AlgebraicGeometry.IdealModuleProductStalk
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Preadditive.Biproducts
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.CoherentKernelCokernelLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.CoherentIdealPatchingExactSequence

/-!
# The integral-support induction step for coherent devissage

Source: Stacks Project, Cohomology of Schemes, Lemma 01YL.
(blueprint: lem-weil-pbc-coherent-property-integral-ideals-of-small-support).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits ZeroObject AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

/-- The generic-point patching step of higher-rank coherent devissage: assuming the
property for coherent modules supported on this integral closed subscheme and vanishing
at its generic point, the distinguished module gives the property for every ideal.

Source: Stacks Project, Cohomology of Schemes, Lemma 01YL, third paragraph and its end,
with the explicit zero hypothesis needed for the zero ideal.
(blueprint: lem-weil-pbc-coherent-property-integral-ideals-of-small-support)

Proof:
1. Extension closure and P(0) give isomorphism invariance: use 0 → 0 → F → G → 0
for an isomorphism F ≅ G of coherent modules. All proper-support cokernels below have
P by hsmall; no induction on smaller integral subschemes is needed in this lemma.
2. Generic-point uniqueness identifies ξ with i(η). Apply the generic-point
ideal-inclusion lemma to G. It embeds a finite direct sum of
a coherent ideal I on Z into G, isomorphically near ξ. The nonzero generic stalk of G
forces both I nonzero and the number r of summands positive. Pushforward commutes with
finite sums. For every nonzero ideal I' contained in I, compose the sum of its inclusions
with this embedding to obtain a mono β : (i_* I')^{⊕ r} → G, bijective at ξ.
3. Its coherent cokernel Q is supported in i(Z) and misses ξ. The annihilator J of Q is
quasi-coherent and coherent: it is the kernel of the structure-sheaf quotient for its
closed subscheme, whose structure sheaf has coherent finite pushforward. On the open
complement of Supp(Q), all stalks of Q vanish, so Q restricts to zero by stalk detection.
Its annihilator is the unit ideal there; in particular J has full stalk at ξ.
Moreover JG is contained in the image of β: multiplication
by J followed by the cokernel map is zero. Apply hG to J to get G' contained in JG, with
full generic stalk and P(G'). Pull it back through the mono β. The resulting coherent
submodule H of (i_* I')^{⊕ r} is isomorphic to G'. Its cokernel misses ξ and is supported
in i(Z), hence has P by hsmall. Extension closure gives P((i_* I')^{⊕ r}); hP_sum gives
P(i_* I').
4. For an arbitrary nonzero ideal I'', the intersection I'' ∩ I is nonzero: on a nonempty
affine open the product of nonzero sections is nonzero since Z is integral. Apply step 3
to this intersection. The inclusion into I'' is generically an isomorphism, so its coherent
pushforward cokernel misses ξ and has P by hsmall. Extension closure gives P(i_* I'').
All ideal modules and their pushforwards are coherent, since the source is locally
Noetherian and closed pushforward is finite. For the zero ideal its pushforward is zero;
isomorphism invariance and hP_zero finish.
-/
theorem coherent_property_integral_ideals_of_small_support
    (X : Scheme.{u}) [IsLocallyNoetherian X] [CompactSpace X]
    (P : X.Modules → Prop)
    (hP_zero : P (0 : X.Modules))
    (hP_ext : ∀ (S : ShortComplex X.Modules), S.ShortExact →
      RingedSpace.IsCoherent X.toRingedSpace S.X₁ →
      RingedSpace.IsCoherent X.toRingedSpace S.X₂ →
      RingedSpace.IsCoherent X.toRingedSpace S.X₃ →
      P S.X₁ → P S.X₃ → P S.X₂)
    (hP_sum : ∀ (F : X.Modules) (r : ℕ),
      RingedSpace.IsCoherent X.toRingedSpace F → 1 ≤ r →
      P (@biproduct (Fin r) X.Modules _ _ (fun _ : Fin r ↦ F)
        (HasBiproduct.of_hasProduct (fun _ : Fin r ↦ F))) → P F)
    (Z : Scheme.{u}) (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z]
    (ξ : X) (hclosure : closure ({ξ} : Set X) = Set.range i.base)
    (hsmall : ∀ Q : X.Modules, RingedSpace.IsCoherent X.toRingedSpace Q →
      {x : X | ¬ Subsingleton (Q.presheaf.stalk x)} ⊆ Set.range i.base →
      Subsingleton (Q.presheaf.stalk ξ) → P Q)
    (hG :
      ∃ G : X.Modules,
        RingedSpace.IsCoherent X.toRingedSpace G ∧
        ({x : X | ¬ Subsingleton (G.presheaf.stalk x)} = Set.range i.base) ∧
        (∀ g : X.presheaf.stalk ξ, ∀ m : (RingedSpace.moduleStalkFunctor
          X.toRingedSpace ξ).obj G, g ∈ IsLocalRing.maximalIdeal _ → g • m = 0) ∧
        ∀ (J : X.Modules) (ι : J ⟶ SheafOfModules.unit X.ringCatSheaf)
          [Mono ι] [J.IsQuasicoherent],
          Function.Surjective
            ((RingedSpace.moduleStalkFunctor X.toRingedSpace ξ).map ι).hom →
          ∃ G' : Subobject G,
            RingedSpace.IsCoherent X.toRingedSpace (G' : X.Modules) ∧
            (∃ h : (G' : X.Modules) ⟶ idealModuleProduct ι G,
              G'.arrow = h ≫ idealModuleProductι ι G) ∧
            Function.Surjective ((RingedSpace.moduleStalkFunctor X.toRingedSpace ξ).map
              G'.arrow).hom ∧ P (G' : X.Modules)) :
    ∀ I : Z.IdealSheafData, P ((pushforward i).obj I.toModules)  := by
  have ft_iso_small_support : ∀ {F G : X.Modules} (e : F ≅ G), F.IsFiniteType → G.IsFiniteType := by
    intro F G e hF
    obtain ⟨q, hq⟩ := SheafOfModules.IsFiniteType.exists_localGeneratorsData F
    let q' : G.LocalGeneratorsData :=
      { I := q.I
        X := q.X
        coversTop := q.coversTop
        generators j := (q.generators j).ofEpi
          ((SheafOfModules.overFunctor X.ringCatSheaf (q.X j)).map e.hom) }
    refine { exists_localGeneratorsData := ⟨q', ?_⟩ }
    constructor
    intro j
    have := hq.isFiniteType j
    exact inferInstanceAs ((q.generators j).ofEpi
      ((SheafOfModules.overFunctor X.ringCatSheaf (q.X j)).map e.hom)).IsFiniteType
  have coh_iso_small_support : ∀ {F G : X.Modules} (e : F ≅ G),
      RingedSpace.IsCoherent X.toRingedSpace F →
      RingedSpace.IsCoherent X.toRingedSpace G := by
    intro F G e hF
    obtain ⟨hq, ht⟩ := (isCoherent_iff_isQuasicoherent_and_isFiniteType X F).mp hF
    exact (isCoherent_iff_isQuasicoherent_and_isFiniteType X G).mpr
      ⟨(SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso e hq,
        ft_iso_small_support e ht⟩
  have coh_zero_small_support : ∀ {F : X.Modules},
      RingedSpace.IsCoherent X.toRingedSpace F →
      RingedSpace.IsCoherent X.toRingedSpace (0 : X.Modules) := by
    intro F hF
    have hk := ((isCoherent_kernel_cokernel_biprod_and_submodule X).1 F F hF hF).1 (𝟙 F)
    exact coh_iso_small_support (isZero_kernel_of_mono (𝟙 F)).isoZero hk.1
  have p_iso_small_support : ∀ {F G : X.Modules} (e : F ≅ G),
      RingedSpace.IsCoherent X.toRingedSpace F → P G → P F := by
    intro F G e hF hG
    let S : ShortComplex X.Modules := ShortComplex.mk (0 : 0 ⟶ F) e.hom (by simp)
    have hs : S.ShortExact :=
      { exact := (S.exact_iff_mono rfl).mpr inferInstance }
    exact hP_ext S hs (coh_zero_small_support hF) hF
      (coh_iso_small_support e hF) hP_zero hG
  intro I
  obtain ⟨r, hr, S, hmid, hs, hF, h₁, h₂, h₃, G', hG', ⟨e⟩, hp, hsupport, hzero⟩ :=
    coherent_ideal_patching_exact_sequence X P hP_zero Z i ξ hclosure hG I
  apply hP_sum ((pushforward i).obj I.toModules) r hF hr
  rw [← hmid]
  exact hP_ext S hs h₁ h₂ h₃ (p_iso_small_support e h₁ hp)
    (hsmall S.X₃ h₃ hsupport hzero)

end AlgebraicGeometry.Scheme.Modules
