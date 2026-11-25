/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.StalkZeroLocus

/-!
# Cardinalities of the stalks of constructible sheaves

Let `F` be a sheaf of `Λ`-modules on the small étale site of a scheme `X`.

* If `F` is locally constant, the stalks of `F` at two geometric points over the same point of `X`
  are isomorphic, and the isomorphism class of the stalk is locally constant on `X`: over each
  member of a trivialising cover all stalks are the value of a constant sheaf, and the images of
  the members are open.
* If `X` has Noetherian underlying space and `F` is constructible, the set of points `x` at which
  the stalk of `F` at the geometric point `X.algClosurePoint x` has a given cardinality is
  constructible: on each stratum of a stratification trivialising `F` it is open.

## Main statements

- `AlgebraicGeometry.Etale.nonempty_sheafFiber_iso_of_isLocallyConstantSheaf`: stalks of a locally
  constant sheaf over the same point are isomorphic.
- `AlgebraicGeometry.Etale.isOpen_setOf_natCard_sheafFiber`: the level sets of the stalk
  cardinality of a locally constant sheaf are open.
- `AlgebraicGeometry.Scheme.IsConstructibleSheaf.isConstructible_setOf_natCard`: the level sets of
  the stalk cardinality of a constructible sheaf are constructible.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite Topology

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {Λ : Type (u + 1)} [Ring Λ] {X : Scheme.{u}}
  (I : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))

/-- If the pullback of `I` along an étale `f` is the constant sheaf `N`, the stalk of `I` at a
geometric point in the image of `f` is `N`: the geometric point lifts along `f`, and the stalk of
a constant sheaf is its value. -/
lemma nonempty_sheafFiber_iso_of_iso {V : Scheme.{u}} (f : V ⟶ X) [Etale f]
    {N : ModuleCat.{u + 1} Λ}
    (e : ((f)^*[ModuleCat.{u + 1} Λ]).obj I ≅ (constantSheaf V.smallEtaleTopology _).obj N)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X)
    (hs : s.base (IsLocalRing.closedPoint Ω) ∈ Set.range f.base) :
    Nonempty ((pointSmallEtale s).sheafFiber.obj I ≅ N) := by
  have : PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget (ModuleCat.{u + 1} Λ)) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  obtain ⟨v, hv⟩ := hs
  obtain ⟨t, -⟩ := pointSmallEtaleFiberObjToPreimage_surjective s rfl (Scheme.Etale.mk f)
    ⟨v, by
      change f.base v = s.base default
      rw [hv]
      exact congrArg s.base (Subsingleton.elim _ _)⟩
  have ht : t.left ≫ f = s := Over.w t
  rw [← ht]
  exact ⟨((upperStarCompSheafFiberIso (ModuleCat.{u + 1} Λ) f t.left).app I).symm ≪≫
    (pointSmallEtale t.left).sheafFiber.mapIso e ≪≫
    (pointSmallEtale t.left).sheafFiberConstantSheafIso N⟩

/-- **The stalks of a locally constant sheaf are locally constant.** Every point of `X` has an
open neighbourhood `U` and a module `N` such that the stalk of `I` at every geometric point over
`U` is isomorphic to `N`. -/
lemma exists_isOpen_nonempty_sheafFiber_iso [IsLocallyConstantSheaf I] (x : X) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ ∃ N : ModuleCat.{u + 1} Λ,
      ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X),
        s.base (IsLocalRing.closedPoint Ω) ∈ U →
          Nonempty ((pointSmallEtale s).sheafFiber.obj I ≅ N) := by
  obtain ⟨⟨𝒰, hc⟩⟩ := IsLocallyConstantSheaf.nonempty_locallyConstantDatum (F := I)
  obtain ⟨i, v, rfl⟩ := 𝒰.exists_eq x
  have : Etale (𝒰.f i) := 𝒰.map_prop i
  obtain ⟨N, ⟨e⟩⟩ := ((isConstant_over_iff_upperStar _ (𝒰.etalePrecoverageToEtale i) I).1
    (hc i)).mem_essImage
  exact ⟨_, (𝒰.f i).isOpenMap.isOpen_range, ⟨v, rfl⟩, N,
    fun Ω _ _ s hs ↦ nonempty_sheafFiber_iso_of_iso I (𝒰.f i) e.symm s hs⟩

/-- The stalks of a locally constant sheaf at two geometric points over the same point are
isomorphic. -/
lemma nonempty_sheafFiber_iso_of_isLocallyConstantSheaf [IsLocallyConstantSheaf I]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X)
    {Ω' : Type u} [Field Ω'] [IsSepClosed Ω'] (s' : Spec (.of Ω') ⟶ X)
    (h : s.base (IsLocalRing.closedPoint Ω) = s'.base (IsLocalRing.closedPoint Ω')) :
    Nonempty ((pointSmallEtale s).sheafFiber.obj I ≅ (pointSmallEtale s').sheafFiber.obj I) := by
  obtain ⟨U, -, hU, N, hN⟩ :=
    exists_isOpen_nonempty_sheafFiber_iso I (s.base (IsLocalRing.closedPoint Ω))
  obtain ⟨e⟩ := hN Ω s hU
  obtain ⟨e'⟩ := hN Ω' s' (h ▸ hU)
  exact ⟨e ≪≫ e'.symm⟩

/-- **The level sets of the stalk cardinality of a locally constant sheaf are open.** -/
lemma isOpen_setOf_natCard_sheafFiber [IsLocallyConstantSheaf I] (n : ℕ) :
    IsOpen {x : X | Nat.card ((pointSmallEtale (X.algClosurePoint x)).sheafFiber
      (A := ModuleCat.{u + 1} Λ) |>.obj I) = n} := by
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  obtain ⟨U, hUo, hxU, N, hN⟩ := exists_isOpen_nonempty_sheafFiber_iso I x
  refine ⟨U, fun y hy ↦ ?_, hUo, hxU⟩
  obtain ⟨e⟩ := hN _ (X.algClosurePoint x) (by rw [algClosurePoint_base]; exact hxU)
  obtain ⟨e'⟩ := hN _ (X.algClosurePoint y) (by rw [algClosurePoint_base]; exact hy)
  refine (Nat.card_congr (e' ≪≫ e.symm).toLinearEquiv.toEquiv).trans ?_
  exact hx

/-- Along an immersion `ι : T ⟶ X` with `ι^* F` locally constant, the cardinality of the stalk of
`F` at `ι t` is that of the stalk of `ι^* F` at `t`. -/
lemma natCard_sheafFiber_of_isImmersion {T : Scheme.{u}} (ι : T ⟶ X) [IsImmersion ι]
    [IsLocallyConstantSheaf ((ι)^*[ModuleCat.{u + 1} Λ].obj I)] (t : T) :
    Nat.card ((pointSmallEtale (X.algClosurePoint (ι.base t))).sheafFiber
      (A := ModuleCat.{u + 1} Λ) |>.obj I) =
    Nat.card ((pointSmallEtale (T.algClosurePoint t)).sheafFiber
      (A := ModuleCat.{u + 1} Λ) |>.obj ((ι)^*[ModuleCat.{u + 1} Λ].obj I)) := by
  obtain ⟨t', ht'⟩ := IsImmersion.exists_comp_eq_of_field ι (X.algClosurePoint (ι.base t))
    ⟨t, by rw [algClosurePoint_base]⟩
  have ht't : t'.base (IsLocalRing.closedPoint _) = t := ι.isEmbedding.injective (by
    rw [← Scheme.Hom.comp_apply, ht', algClosurePoint_base])
  obtain ⟨e⟩ := nonempty_sheafFiber_iso_of_isLocallyConstantSheaf
    ((ι)^*[ModuleCat.{u + 1} Λ].obj I) t' (T.algClosurePoint t)
    (by rw [algClosurePoint_base, ht't])
  refine Nat.card_congr ?_
  rw [← ht']
  exact (((upperStarCompSheafFiberIso (ModuleCat.{u + 1} Λ) ι t').app I).symm ≪≫
    e).toLinearEquiv.toEquiv

end Etale

namespace Scheme

variable {Λ : Type (u + 1)} [Ring Λ]

/-- **The level sets of the stalk cardinality of a constructible sheaf are constructible.** Let
`X` have Noetherian underlying space and `F` be a constructible sheaf of `Λ`-modules. For every
`n` the set of points `x` at which the stalk of `F` at `X.algClosurePoint x` has `n` elements is
constructible: on each stratum of a stratification trivialising `F` it is open, by
`AlgebraicGeometry.Etale.isOpen_setOf_natCard_sheafFiber`. -/
theorem IsConstructibleSheaf.isConstructible_setOf_natCard {X : Scheme.{u}}
    [TopologicalSpace.NoetherianSpace X] (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [IsConstructibleSheaf F] (n : ℕ) :
    IsConstructible {x : X | Nat.card ((pointSmallEtale (X.algClosurePoint x)).sheafFiber
      (A := ModuleCat.{u + 1} Λ) |>.obj F) = n} := by
  obtain ⟨S, hS⟩ := IsConstructibleSheaf.exists_stratification
    (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N) (CA := fun M : ModuleCat.{u + 1} Λ ↦ M)
    (F := F)
  set C := {x : X | Nat.card ((pointSmallEtale (X.algClosurePoint x)).sheafFiber
      (A := ModuleCat.{u + 1} Λ) |>.obj F) = n}
  have heq : C = ⋃ i, (S.stratum i ∩ C) := by
    rw [← Set.iUnion_inter, S.iUnion_stratum_eq_univ, Set.univ_inter]
  rw [heq]
  refine IsConstructible.iUnion fun i ↦ ?_
  have := (hS i).toIsLocallyConstantSheaf
  obtain ⟨O, hO, hOe⟩ := (S.immersion i).isEmbedding.isInducing.isOpen_iff.mp
    (Etale.isOpen_setOf_natCard_sheafFiber
      ((Etale.upperStar (ModuleCat.{u + 1} Λ) (S.immersion i)).obj F) n)
  have : S.stratum i ∩ C = S.stratum i ∩ O := by
    rw [← S.range_immersion]
    ext x
    constructor
    · rintro ⟨⟨t, rfl⟩, hx⟩
      refine ⟨⟨t, rfl⟩, ?_⟩
      change t ∈ (S.immersion i).base ⁻¹' O
      rw [hOe]
      exact (Etale.natCard_sheafFiber_of_isImmersion F (S.immersion i) t).symm.trans hx
    · rintro ⟨⟨t, rfl⟩, hx⟩
      refine ⟨⟨t, rfl⟩, ?_⟩
      change t ∈ (S.immersion i).base ⁻¹' O at hx
      rw [hOe] at hx
      exact (Etale.natCard_sheafFiber_of_isImmersion F (S.immersion i) t).trans hx
  rw [this]
  exact (S.isConstructible_stratum i).inter hO.isConstructible_of_noetherianSpace

end Scheme

end AlgebraicGeometry

namespace AlgebraicGeometry.Etale

open Scheme

variable {Λ : Type (u + 1)} [CommRing Λ] {X : Scheme.{u}}

/-- A morphism `d : G ⟶ F` is surjective on the stalk at a geometric point, where the stalk of `F`
is finite, exactly when the stalk of the coimage of `d` has as many elements as the stalk of
`F`: the stalk of the coimage injects into that of `F` with the image of `d` as range. -/
lemma surjective_sheafFiber_map_iff_natCard_coimage
    {G F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (d : G ⟶ F) {Ω : Type u} [Field Ω]
    [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X)
    [Finite ((pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ) |>.obj F)] :
    Function.Surjective ((pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ) |>.map d) ↔
      Nat.card ((pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ) |>.obj
        (Abelian.coimage d)) =
        Nat.card ((pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ) |>.obj F) := by
  set Φ := (pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)
  have hinj : Function.Injective (Φ.map (Abelian.factorThruCoimage d)) :=
    (ModuleCat.mono_iff_injective _).1 (Φ.map_mono _)
  have hsurj : Function.Surjective (Φ.map (Abelian.coimage.π d)) :=
    (ModuleCat.epi_iff_surjective _).1 (Φ.map_epi _)
  have hfac : Φ.map d = Φ.map (Abelian.coimage.π d) ≫ Φ.map (Abelian.factorThruCoimage d) := by
    rw [← Φ.map_comp, Abelian.coimage.fac]
  constructor
  · intro h
    refine Nat.card_congr (Equiv.ofBijective _ ⟨hinj, fun y ↦ ?_⟩)
    obtain ⟨z, rfl⟩ := h y
    exact ⟨Φ.map (Abelian.coimage.π d) z, by rw [hfac, ConcreteCategory.comp_apply]⟩
  · intro h y
    obtain ⟨z, rfl⟩ := (hinj.bijective_of_nat_card_le h.ge).2 y
    obtain ⟨w, rfl⟩ := hsurj z
    exact ⟨w, by rw [hfac, ConcreteCategory.comp_apply]⟩

end AlgebraicGeometry.Etale
