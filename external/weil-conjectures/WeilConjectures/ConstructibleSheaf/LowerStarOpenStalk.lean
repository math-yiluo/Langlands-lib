/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.DenseOpenUnit

/-!
# Finiteness of the stalks of a direct image along an open immersion

Let `X` be a locally noetherian scheme such that the local rings of all étale `X`-schemes are
integral domains (for instance a regular scheme), `j : U ⟶ X` an open immersion and `F` a
locally constant sheaf of modules on the small étale site of `U` whose geometric stalks are
finite of bounded cardinality. Then the geometric stalks of `j_* F` are finite.

An element of the stalk of `j_* F` at a geometric point is the germ of a section of `F` over
`V ×_X U` for an étale neighbourhood `V`; finitely many germs come from one neighbourhood, the
fibre category of a point being cofiltered, and this neighbourhood may be shrunk to have
irreducible underlying space. Then `V ×_X U` is a nonempty open of `V`, hence irreducible, or
empty, and the sections of a locally constant sheaf over an étale scheme with connected
underlying space inject into the stalk at any geometric point of it
(`AlgebraicGeometry.Etale.injective_toPresheafFiber_of_preconnectedSpace`). So the stalk of
`j_* F` has at most as many elements as the largest stalk of `F`.

The cardinalities of the stalks of a finite locally constant sheaf of modules over a finite ring
on a quasi-compact scheme are bounded
(`AlgebraicGeometry.Etale.exists_natCard_sheafFiber_le`): finitely many members of a
trivialising cover suffice, and over each of them all stalks are the value of a constant sheaf.

## Main statements

- `AlgebraicGeometry.Etale.injective_toPresheafFiber_of_preconnectedSpace`
- `AlgebraicGeometry.Etale.finite_sheafFiber_lowerStar`
- `AlgebraicGeometry.Etale.exists_natCard_sheafFiber_le`
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {Λ : Type (u + 1)} [Ring Λ]

section Injective

variable {X : Scheme.{u}} (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))

/-- **Sections of a locally constant sheaf over a connected étale scheme inject into stalks.**
For a locally constant sheaf `M` of modules and an étale `X`-scheme `W` with connected underlying
space, the germ map from the sections over `W` to the stalk at any geometric point of `W` is
injective: a section with vanishing germ vanishes near a point, hence everywhere. -/
lemma injective_toPresheafFiber_of_preconnectedSpace [IsLocallyConstantSheaf M]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X) {W : X.Etale}
    [PreconnectedSpace W.left] (w : (pointSmallEtale s).fiber.obj W) :
    Function.Injective ((pointSmallEtale s).toPresheafFiber W w M.obj) := by
  have : PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget (ModuleCat.{u + 1} Λ)) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  intro a b hab
  rw [← sub_eq_zero]
  obtain ⟨Y, f, y, hy, hf⟩ := ((pointSmallEtale s).toPresheafFiber_eq_iff' W w a b).1 hab
  refine eq_zero_of_mem_moduleVanishingLocus (w := w.left (IsLocalRing.closedPoint Ω))
    ⟨Y, f, y.left (IsLocalRing.closedPoint Ω), ?_, ?_⟩
  · rw [← hy]
    rfl
  · rw [map_sub, hf, sub_self]

/-- The sections of a sheaf over an étale scheme with empty underlying space are all equal, the
empty sieve covering it. -/
lemma subsingleton_obj_of_isEmpty {W : X.Etale} [IsEmpty W.left] :
    Subsingleton (ToType (M.obj.obj (op W))) := by
  refine ⟨fun a b ↦ Sheaf.isSeparated M W ⊥ ?_ a b fun _ _ h ↦ h.elim⟩
  rw [mem_smallEtaleTopology_iff]
  exact fun w ↦ isEmptyElim w

end Injective

section LowerStar

variable {X U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- **Sections of a locally constant sheaf over the punctured part of an irreducible
neighbourhood are bounded.** Let `W` be an étale `X`-scheme with irreducible underlying space and
`F` a locally constant sheaf of modules on `U` all of whose geometric stalks are finite with at
most `B` elements. Then the sections of `j_* F` over `W`, the sections of `F` over `W ×_X U`, are
finite with at most `max B 1` elements. -/
lemma finite_and_natCard_le_of_irreducibleSpace
    (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsLocallyConstantSheaf F] (B : ℕ)
    (hB : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ U),
      Finite (ToType ((pointSmallEtale s).sheafFiber.obj F)) ∧
        Nat.card (ToType ((pointSmallEtale s).sheafFiber.obj F)) ≤ B)
    (W : X.Etale) [IrreducibleSpace W.left] :
    Finite (ToType (((j)_*[ModuleCat.{u + 1} Λ].obj F).obj.obj (op W))) ∧
      Nat.card (ToType (((j)_*[ModuleCat.{u + 1} Λ].obj F).obj.obj (op W))) ≤ max B 1 := by
  let WU := (MorphismProperty.Over.pullback @Etale ⊤ j).obj W
  change Finite (ToType (F.obj.obj (op WU))) ∧ Nat.card (ToType (F.obj.obj (op WU))) ≤ max B 1
  rcases isEmpty_or_nonempty WU.left with hWU | ⟨⟨z⟩⟩
  · have := subsingleton_obj_of_isEmpty F (W := WU)
    exact ⟨inferInstance, (Finite.card_le_one_iff_subsingleton.2 this).trans (le_max_right _ _)⟩
  have : PreconnectedSpace WU.left :=
    preconnectedSpace_pullback_of_irreducibleSpace (W := W.left) (X := X) W.hom j
  let y := U.algClosurePoint (WU.hom z)
  obtain ⟨t, -⟩ := pointSmallEtaleFiberObjToPreimage_surjective y
    (U.algClosurePoint_base (WU.hom z) _) WU ⟨z, rfl⟩
  have hinj := injective_toPresheafFiber_of_preconnectedSpace F y t
  obtain ⟨hfin, hcard⟩ := hB _ y
  have : Finite ↑((pointSmallEtale y).presheafFiber.obj F.obj) := hfin
  have : Finite (ToType (F.obj.obj (op WU))) := Finite.of_injective _ hinj
  exact ⟨this, ((Nat.card_le_card_of_injective _ hinj).trans hcard).trans (le_max_left _ _)⟩

/-- **The stalks of a direct image along an open immersion into a regular scheme are finite.**
Let `X` be a locally noetherian scheme such that the local rings of all étale `X`-schemes are
integral domains, `j : U ⟶ X` an open immersion and `F` a locally constant sheaf of modules on
`U` whose geometric stalks are finite with at most `B` elements. Then the geometric stalks of
`j_* F` are finite: finitely many germs are germs of sections over one étale neighbourhood,
which may be taken irreducible, and there are at most `max B 1` of them
(`AlgebraicGeometry.Etale.finite_and_natCard_le_of_irreducibleSpace`). -/
theorem finite_sheafFiber_lowerStar
    (hX : ∀ (W : X.Etale) (w : W.left), IsDomain (W.left.presheaf.stalk w))
    [IsLocallyNoetherian X] (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [IsLocallyConstantSheaf F] (B : ℕ)
    (hB : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ U),
      Finite (ToType ((pointSmallEtale s).sheafFiber.obj F)) ∧
        Nat.card (ToType ((pointSmallEtale s).sheafFiber.obj F)) ≤ B)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X) :
    Finite (ToType ((pointSmallEtale s).sheafFiber.obj ((j)_*[ModuleCat.{u + 1} Λ].obj F))) := by
  have : PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget (ModuleCat.{u + 1} Λ)) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  let Φ := pointSmallEtale s
  let J := (j)_*[ModuleCat.{u + 1} Λ].obj F
  -- every element of the fibre category is refined by one with irreducible underlying space
  have key (E : Φ.fiber.Elements) : ∃ (W : X.Etale) (w : Φ.fiber.obj W) (k : W ⟶ E.1),
      Φ.fiber.map k w = E.2 ∧ IrreducibleSpace W.left := by
    obtain @⟨V, v⟩ := E
    have : IsLocallyNoetherian V.left := LocallyOfFiniteType.isLocallyNoetherian (Y := X) V.hom
    obtain ⟨O, hO, hOirr⟩ := exists_isOpen_irreducibleSpace_of_isDomain_stalk (hX V)
      (v.left (IsLocalRing.closedPoint Ω))
    obtain ⟨v', hv'⟩ := exists_pointSmallEtale_fiber_ofOpens s v O (by
      rintro _ ⟨z, rfl⟩
      have : Subsingleton (Spec (.of Ω)) := inferInstanceAs (Subsingleton (PrimeSpectrum Ω))
      rwa [@Subsingleton.elim (Spec (.of Ω)) this z (IsLocalRing.closedPoint Ω)])
    exact ⟨Etale.ofOpens V O, v', Etale.ofOpensι V O, hv', hOirr⟩
  by_contra hinf
  rw [not_finite_iff_infinite] at hinf
  obtain ⟨T, hT⟩ := Infinite.exists_subset_card_eq (ToType (Φ.sheafFiber.obj J)) (max B 1 + 1)
  -- representatives of the elements of `T`
  have hrep (p : ToType (Φ.sheafFiber.obj J)) :
      ∃ (E : Φ.fiber.Elements) (σ : ToType (J.obj.obj (op E.1))),
      Φ.toPresheafFiber E.1 E.2 J.obj σ = p := by
    obtain ⟨V, v, σ, hσ⟩ := Φ.toPresheafFiber_jointly_surjective p
    exact ⟨Φ.fiber.elementsMk V v, σ, hσ⟩
  choose E σ hσ using hrep
  classical
  obtain ⟨E₀, hE₀⟩ := IsCofiltered.inf_objs_exists (T.image E)
  obtain ⟨W, w, k, hk, hW⟩ := key E₀
  let f (p : T) : E₀ ⟶ E p := (hE₀ (Finset.mem_image_of_mem E p.2)).some
  -- the restrictions of the representatives to `W` determine the elements of `T`
  let r (p : T) : ToType (J.obj.obj (op W)) := J.obj.map (k ≫ (f p).1).op (σ p)
  have hr (p : T) : Φ.toPresheafFiber W w J.obj (r p) = p.1 := by
    have := Φ.toPresheafFiber_w_apply (k ≫ (f p).1) w J.obj (σ p)
    rw [CategoryTheory.Functor.map_comp_apply, hk, (f p).2] at this
    exact this.trans (hσ p)
  have hrinj : Function.Injective r := fun p q h ↦ Subtype.ext ((hr p).symm.trans
    ((congrArg _ h).trans (hr q)))
  obtain ⟨hfin, hcard⟩ := finite_and_natCard_le_of_irreducibleSpace j F B hB W
  have hcard' : Nat.card (ToType (J.obj.obj (op W))) ≤ max B 1 := hcard
  have : Finite (ToType (J.obj.obj (op W))) := hfin
  have := Nat.card_le_card_of_injective r hrinj
  rw [Nat.card_eq_fintype_card, Fintype.card_coe, hT] at this
  omega

end LowerStar

section Bound

variable {X : Scheme.{u}} [Finite Λ]

/-- **The stalks of a finite locally constant sheaf on a quasi-compact scheme are uniformly
bounded.** For a finite locally constant sheaf `F` of modules over a finite ring on a
quasi-compact scheme `X`, the geometric stalks of `F` are finite of bounded cardinality: finitely
many members of a trivialising cover cover `X`, and the stalks at the geometric points of a
member over which `F` is the constant sheaf `N` are `N`. -/
theorem exists_natCard_sheafFiber_le [CompactSpace X]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsFiniteLocallyConstantSheaf F] :
    ∃ B : ℕ, ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X),
      Finite (ToType ((pointSmallEtale s).sheafFiber.obj F)) ∧
        Nat.card (ToType ((pointSmallEtale s).sheafFiber.obj F)) ≤ B := by
  have : PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget (ModuleCat.{u + 1} Λ)) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  obtain ⟨⟨𝒰, hc⟩⟩ := IsLocallyConstantSheaf.nonempty_locallyConstantDatum (F := F)
  have hN (i : 𝒰.I₀) : ∃ N : ModuleCat.{u + 1} Λ,
      Nonempty (((𝒰.f i))^*[ModuleCat.{u + 1} Λ].obj F ≅
        (constantSheaf (𝒰.X i).smallEtaleTopology _).obj N) := by
    have : Etale (𝒰.f i) := 𝒰.map_prop i
    obtain ⟨N, ⟨e⟩⟩ := ((isConstant_over_iff_upperStar _ (𝒰.etalePrecoverageToEtale i) F).1
      (hc i)).mem_essImage
    exact ⟨N, ⟨e.symm⟩⟩
  choose N e using hN
  have hopen (i : 𝒰.I₀) : IsOpen (Set.range (𝒰.f i).base) :=
    have : Etale (𝒰.f i) := 𝒰.map_prop i
    (𝒰.f i).isOpenMap.isOpen_range
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun i ↦ Set.range (𝒰.f i).base) hopen
    fun x _ ↦ by
      obtain ⟨i, y, rfl⟩ := 𝒰.exists_eq x
      exact Set.mem_iUnion.2 ⟨i, y, rfl⟩
  refine ⟨∑ i ∈ t, Nat.card (ToType (N i)), fun Ω _ _ s ↦ ?_⟩
  have hfin : Finite (ToType ((pointSmallEtale s).sheafFiber.obj F)) := by
    have := (ModuleCat.isFinitelyGenerated_iff _).1
      (IsFiniteSheaf.isFinitelyGenerated_sheafFiber (F := F) Ω s)
    exact Module.finite_of_finite Λ
  refine ⟨hfin, ?_⟩
  obtain ⟨i, hi, hsi⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ (s.base default)))
  have : Etale (𝒰.f i) := 𝒰.map_prop i
  obtain ⟨y, hy⟩ := hsi
  obtain ⟨l, hl, -⟩ := exists_fac_of_etale_of_isSepClosed (𝒰.f i) s y hy
  subst hl
  have := (e i).some
  let iso := ((upperStarCompSheafFiberIso (ModuleCat.{u + 1} Λ) (𝒰.f i) l).app F).symm ≪≫
    (pointSmallEtale l).sheafFiber.mapIso (e i).some ≪≫
    (pointSmallEtale l).sheafFiberConstantSheafIso (N i)
  rw [Nat.card_congr iso.toLinearEquiv.toEquiv]
  exact Finset.single_le_sum (f := fun i ↦ Nat.card (ToType (N i))) (fun _ _ ↦ Nat.zero_le _) hi

end Bound

end Etale

end AlgebraicGeometry
