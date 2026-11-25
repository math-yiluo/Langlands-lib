/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.AlgebraicGeometry.Sites.DivisorMap
public import WeilConjectures.Mathlib.AlgebraicGeometry.FunctionField
public import WeilConjectures.Mathlib.AlgebraicGeometry.Stalk
public import WeilConjectures.Mathlib.Topology.NoetherianSpace

/-!
# Local structure of divisors on étale neighbourhoods

Let `X` be an integral regular locally noetherian scheme with generic point
`i : Spec k(X) ⟶ X`, and `V` an étale `X`-scheme. The local rings of `V` are regular, hence
unique factorisation domains, and the local generic ring of `V` at a point `y` is the fraction
field of `𝒪_{V,y}` (`AlgebraicGeometry.Scheme.Etale.isFractionRing_localGenericRing`). This file
collects the local facts about the divisors of functions on the generic fibre of `V` which enter
the proof of the exactness of the divisor sequence.

## Main statements

- `AlgebraicGeometry.Scheme.exists_opens_isPreirreducible`: a point whose local ring is a domain
  has an irreducible open neighbourhood.
- `AlgebraicGeometry.Scheme.Etale.injective_toLocalGenericRing`: on an integral quasi-separated
  étale `X`-scheme, a function on the generic fibre is determined by its image in the local
  generic ring at any point.
- `AlgebraicGeometry.Scheme.Etale.exists_specializes_comap_eq_span`: the prime elements of the
  local ring `𝒪_{V,y}` correspond to the points of codimension one generalising `y`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite Order TopologicalSpace

namespace AlgebraicGeometry.Scheme

/-- A point whose local ring is a domain has an irreducible open neighbourhood: the
generalisations of `y` are the images of the primes of `𝒪_{V,y}`, which all contain the zero
ideal, so `y` lies in a single irreducible component of a noetherian open neighbourhood. -/
lemma exists_opens_isPreirreducible {V : Scheme.{u}} [IsLocallyNoetherian V] (y : V)
    [IsDomain (V.presheaf.stalk y)] :
    ∃ W : V.Opens, y ∈ W ∧ IsPreirreducible (W : Set V) := by
  obtain ⟨_, ⟨U₀, hU₀, rfl⟩, hyU₀, -⟩ :=
    V.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
  have : NoetherianSpace U₀ := @noetherianSpace_of_isAffineOpen _ U₀ hU₀
    (IsLocallyNoetherian.component_noetherian ⟨U₀, hU₀⟩)
  have : QuasiSober U₀ := inferInstanceAs (QuasiSober (Scheme.Opens.toScheme (X := V) U₀))
  -- the generic point of `Spec 𝒪_{V,y}` generalises every generalisation of `y`
  let c : V := V.fromSpecStalk y ⟨⊥, Ideal.isPrime_bot⟩
  have hc : ∀ a : V, a ⤳ y → c ⤳ a := by
    intro a ha
    have ha' : a ∈ Set.range (V.fromSpecStalk y) := by rw [Scheme.range_fromSpecStalk]; exact ha
    obtain ⟨p, rfl⟩ := ha'
    exact ((PrimeSpectrum.le_iff_specializes _ _).1 bot_le).map (V.fromSpecStalk y).continuous
  have hcU₀ : c ∈ U₀ := (hc y specializes_rfl).mem_open U₀.2 hyU₀
  -- hence `y` lies in a unique irreducible component of `U₀`
  obtain ⟨W₀, hW₀, hyW₀, hirr⟩ := NoetherianSpace.exists_isOpen_isPreirreducible
    (α := U₀) ⟨y, hyU₀⟩ fun Z₁ hZ₁ Z₂ hZ₂ h₁ h₂ ↦ by
      have key (Z : Set U₀) (hZ : Z ∈ irreducibleComponents U₀) (h : ⟨y, hyU₀⟩ ∈ Z) :
          Z = closure {⟨c, hcU₀⟩} := by
        obtain ⟨g, hg⟩ := QuasiSober.sober hZ.1 (isClosed_of_mem_irreducibleComponents _ hZ)
        have hcg : (⟨c, hcU₀⟩ : U₀) ⤳ g :=
          (Topology.IsInducing.subtypeVal.specializes_iff).1
            (hc g.1 ((hg.specializes h).map continuous_subtype_val))
        have hsub : Z ⊆ closure {⟨c, hcU₀⟩} := by
          rw [← hg.def]
          exact specializes_iff_closure_subset.1 hcg
        exact ((hZ.2 isIrreducible_singleton.closure hsub).antisymm hsub).symm
      rw [key Z₁ hZ₁ h₁, key Z₂ hZ₂ h₂]
  refine ⟨⟨Subtype.val '' W₀, U₀.2.isOpenMap_subtype_val W₀ hW₀⟩, ⟨_, hyW₀, rfl⟩,
    hirr.image _ continuous_subtype_val.continuousOn⟩

/-- A germ at `y` is the germ of a section over an affine open neighbourhood of `y` inside any
given open neighbourhood. -/
lemma exists_isAffineOpen_germ_eq {V : Scheme.{u}} {y : V} {N : V.Opens} (hyN : y ∈ N)
    (t : V.presheaf.stalk y) :
    ∃ (U : V.Opens) (_ : IsAffineOpen U) (hyU : y ∈ U) (_ : U ≤ N) (s : Γ(V, U)),
      V.presheaf.germ U y hyU s = t := by
  obtain ⟨U₁, hyU₁, s₁, hs₁⟩ := V.presheaf.exists_germ_eq t
  obtain ⟨_, ⟨U, hU, rfl⟩, hyU, hUle⟩ :=
    V.isBasis_affineOpens.exists_subset_of_mem_open (show y ∈ U₁ ⊓ N from ⟨hyU₁, hyN⟩)
      (U₁ ⊓ N).isOpen
  refine ⟨U, hU, hyU, fun z hz ↦ (hUle hz).2, V.presheaf.map (homOfLE fun z hz ↦ (hUle hz).1).op s₁,
    ?_⟩
  rw [V.presheaf.germ_res_apply]
  exact hs₁

/-- A unit of the local ring at `y` is the germ of a unit over an affine open neighbourhood of `y`
inside any given open neighbourhood. -/
lemma exists_isAffineOpen_isUnit_germ_eq {V : Scheme.{u}} {y : V} {N : V.Opens} (hyN : y ∈ N)
    (r : (V.presheaf.stalk y)ˣ) :
    ∃ (U : V.Opens) (_ : IsAffineOpen U) (hyU : y ∈ U) (_ : U ≤ N) (s : Γ(V, U)),
      IsUnit s ∧ V.presheaf.germ U y hyU s = r := by
  obtain ⟨U₁, hU₁, hyU₁, hU₁N, s₁, hs₁⟩ := exists_isAffineOpen_germ_eq hyN r.val
  have hyD : y ∈ V.basicOpen s₁ := (V.mem_basicOpen s₁ y hyU₁).2 (hs₁ ▸ r.isUnit)
  refine ⟨V.basicOpen s₁, hU₁.basicOpen s₁, hyD, (V.basicOpen_le s₁).trans hU₁N,
    V.presheaf.map (homOfLE (V.basicOpen_le s₁)).op s₁, V.toRingedSpace.isUnit_res_basicOpen s₁,
    ?_⟩
  rw [V.presheaf.germ_res_apply]
  exact hs₁

/-- An open subscheme of a scheme with reduced local rings, contained in a preirreducible set and
containing a point, is integral. -/
lemma isIntegral_of_isPreirreducible {V : Scheme.{u}} [IsReduced V] {U : V.Opens} {y : V}
    (hyU : y ∈ U) {W : Set V} (hW : IsPreirreducible W) (hUW : (U : Set V) ⊆ W) :
    IsIntegral U.toScheme := by
  have : Nonempty U := ⟨⟨y, hyU⟩⟩
  have : IrreducibleSpace U := Subtype.irreducibleSpace
    ⟨⟨y, hyU⟩, hW.open_subset U.2 hUW⟩
  have : IsReduced U.toScheme := isReduced_of_isOpenImmersion U.ι
  exact isIntegral_of_irreducibleSpace_of_isReduced _

namespace Etale

variable {X : Scheme.{u}} [IsIntegral X]

/-- **Functions on the generic fibre are determined locally.** Let `X` be an integral scheme and
`V` an étale `X`-scheme which is integral and quasi-separated. Then a function on the generic
fibre `V ×_X Spec k(X)` is determined by its image in the local generic ring at any point `y`:
`Spec 𝒪_{V,y} ⟶ V` is scheme-theoretically dominant, and stays so after the flat base change to
the generic fibre. -/
lemma injective_toLocalGenericRing (V : X.Etale) [IsIntegral V.left]
    [QuasiSeparatedSpace V.left] (y : V.left) :
    Function.Injective (toLocalGenericRing V y) := by
  have : IsDominant (V.left.fromSpecStalk y) := by
    rw [isDominant_iff, DenseRange, range_fromSpecStalk]
    refine dense_iff_closure_eq.2 (Set.eq_univ_of_univ_subset ?_)
    rw [← (genericPoint_spec V.left).def]
    exact closure_mono (Set.singleton_subset_iff.2 ((genericPoint_spec V.left).specializes trivial))
  have : IsSchemeTheoreticallyDominant (V.left.fromSpecStalk y) := .of_isDominant _
  have : QuasiCompact (V.left.fromSpecStalk y) := quasiCompact_of_compactSpace _
  let m := pullback.map (V.left.fromSpecStalk y ≫ V.hom) X.fromSpecFunctionField V.hom
    X.fromSpecFunctionField (V.left.fromSpecStalk y) (𝟙 _) (𝟙 _) (by simp) (by simp)
  have H : IsPullback (pullback.fst _ _) m (V.left.fromSpecStalk y)
      (pullback.fst V.hom X.fromSpecFunctionField) := by
    refine IsPullback.of_bot ?_ (by simp [m]) (IsPullback.of_hasPullback V.hom _)
    have : m ≫ pullback.snd V.hom X.fromSpecFunctionField =
        pullback.snd (V.left.fromSpecStalk y ≫ V.hom) X.fromSpecFunctionField := by
      simp [m]
    rw [this]
    exact IsPullback.of_hasPullback _ _
  have : Flat X.fromSpecFunctionField := Scheme.flat_fromSpecStalk _ _
  have : IsSchemeTheoreticallyDominant m := IsSchemeTheoreticallyDominant.of_isPullback H
  have : QuasiCompact m := MorphismProperty.of_isPullback H inferInstance
  exact m.app_injective ⊤

/-- The germ at a point of an open subscheme `U` of a section over `U`, transported to `U`. -/
lemma germ_topIso_inv {V : Scheme.{u}} (U : V.Opens) (a : Γ(V, U)) (z : U) :
    U.toScheme.presheaf.germ ⊤ z trivial (U.topIso.inv a) =
      (U.stalkIso z).inv (V.presheaf.germ U z z.2 a) := by
  rw [← Scheme.Opens.germ_stalkIso_inv U ⊤ z trivial, Scheme.Opens.topIso_inv,
    CommRingCat.comp_apply]
  congr 1
  exact V.presheaf.germ_res_apply _ _ _ _

/-- The map `Γ(Spec 𝒪_{V,y} ×_X Spec k(X), 𝒪) ⟶ Γ(Spec 𝒪_{V,w} ×_X Spec k(X), 𝒪)` of local generic
rings induced by a generalisation `w ⤳ y`. -/
noncomputable def localGenericRingSpecializes (V : X.Etale) {w y : V.left} (h : w ⤳ y) :
    localGenericRing V y ⟶ localGenericRing V w :=
  (pullback.map _ _ _ _ (Spec.map (V.left.presheaf.stalkSpecializes h)) (𝟙 _) (𝟙 _)
    (by rw [Category.comp_id, SpecMap_stalkSpecializes_fromSpecStalk_assoc]) (by simp)).appTop

lemma toLocalGenericRing_comp_localGenericRingSpecializes (V : X.Etale) {w y : V.left}
    (h : w ⤳ y) :
    toLocalGenericRing V y ≫ localGenericRingSpecializes V h = toLocalGenericRing V w := by
  rw [toLocalGenericRing, toLocalGenericRing, localGenericRingSpecializes,
    ← Scheme.Hom.comp_appTop, pullback.map_comp]
  congr 2
  exact SpecMap_stalkSpecializes_fromSpecStalk h

lemma stalkToLocalGenericRing_comp_localGenericRingSpecializes (V : X.Etale) {w y : V.left}
    (h : w ⤳ y) :
    stalkToLocalGenericRing V y ≫ localGenericRingSpecializes V h =
      V.left.presheaf.stalkSpecializes h ≫ stalkToLocalGenericRing V w := by
  rw [stalkToLocalGenericRing, stalkToLocalGenericRing, localGenericRingSpecializes,
    Category.assoc, ← Scheme.Hom.comp_appTop, pullback.lift_fst, Scheme.Hom.comp_appTop,
    ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality, Category.assoc]

/-- In an algebra, `φ * b = a` with `b` a unit means that `φ` is the image of `a b⁻¹`. -/
lemma _root_.eq_algebraMap_mul_inv_of_mul_eq {A L : Type*} [CommRing A] [CommRing L]
    [Algebra A L] {φ : L} {a b : A} (hb : IsUnit b) (h : φ * algebraMap A L b = algebraMap A L a) :
    φ = algebraMap A L (a * ↑hb.unit⁻¹) := by
  rw [map_mul, ← h, mul_assoc, ← map_mul, IsUnit.mul_val_inv, map_one, mul_one]

variable [IsRegular X]

omit [IsRegular X] in
/-- The image in the local generic ring at a point `z` of an open `U` of a function on `V`,
restricted to the generic fibre of `U`. -/
lemma toLocalGenericRing_map_ofOpensι (V : X.Etale) (U : V.left.Opens) (z : U)
    (f : Γ(pullback V.hom X.fromSpecFunctionField, ⊤)) :
    toLocalGenericRing (ofOpens V U) z
        (((MorphismProperty.Over.pullback @Etale ⊤ X.fromSpecFunctionField).map
          (ofOpensι V U)).left.appTop f) =
      localGenericRingMap (ofOpensι V U) z (toLocalGenericRing V z.1 f) :=
  (congrArg (fun g ↦ g.hom f) (toLocalGenericRing_comp_localGenericRingMap (ofOpensι V U) z)).symm

omit [IsRegular X] in
/-- The image in the local generic ring at a point `z` of an open `U` of a section of `𝒪_V` over
`U`, pulled back to the generic fibre of `U`. -/
lemma toLocalGenericRing_fst_topIso_inv (V : X.Etale) (U : V.left.Opens) (a : Γ(V.left, U))
    (z : U) :
    toLocalGenericRing (ofOpens V U) z
        ((pullback.fst (ofOpens V U).hom X.fromSpecFunctionField).appTop (U.topIso.inv a)) =
      localGenericRingMap (ofOpensι V U) z
        (stalkToLocalGenericRing V z.1 (V.left.presheaf.germ U z z.2 a)) := by
  refine (toLocalGenericRing_fst_appTop (ofOpens V U) z (U.topIso.inv a)).trans ?_
  refine (congrArg _ ((germ_topIso_inv U a z).trans
    (congrArg (fun g ↦ g.hom (V.left.presheaf.germ U z z.2 a))
      (Scheme.Opens.stalkIso_inv U z)))).trans ?_
  exact (congrArg (fun g ↦ g.hom (V.left.presheaf.germ U z z.2 a))
    (stalkToLocalGenericRing_comp_localGenericRingMap (ofOpensι V U) z)).symm

/-- A function on the generic fibre which is a quotient `a / b` of functions on `V` invertible
at `z` has order `0` at `z`. -/
lemma ord_eq_zero_of_mul_eq (W : X.Etale) (z : W.left)
    (g : Γ(pullback W.hom X.fromSpecFunctionField, ⊤)ˣ) (a b : Γ(W.left, ⊤))
    (h : g.val * (pullback.fst W.hom X.fromSpecFunctionField).appTop b =
      (pullback.fst W.hom X.fromSpecFunctionField).appTop a)
    (ha : z ∈ W.left.basicOpen a) (hb : z ∈ W.left.basicOpen b) : ord W z g = 0 := by
  by_cases hcoh : coheight (W.hom z) = 1
  · rw [ord, ite_eq_left hcoh]
    have := isDiscreteValuationRing_stalk W hcoh
    let := (stalkToLocalGenericRing W z).hom.toAlgebra
    have := isFractionRing_localGenericRing W z
    have ha' := (W.left.mem_basicOpen_top a z).1 ha
    have hb' := (W.left.mem_basicOpen_top b z).1 hb
    have h' := congrArg (toLocalGenericRing W z).hom h
    rw [map_mul, toLocalGenericRing_fst_appTop, toLocalGenericRing_fst_appTop] at h'
    rw [eq_algebraMap_mul_inv_of_mul_eq hb' h']
    exact Ring.ordOf_algebraMap_of_isUnit (ha'.mul hb'.unit⁻¹.isUnit)
  · exact ord_of_coheight_ne_one W hcoh _

/-- A point with a generalisation other than itself and the generic point does not have
codimension one. -/
lemma _root_.AlgebraicGeometry.Scheme.coheight_ne_one_of_specializes {S : Scheme.{u}}
    [IrreducibleSpace S] {z c : S} (hcz : c ⤳ z) (hne : c ≠ z) (hc : c ≠ genericPoint S) :
    coheight z ≠ 1 := by
  have h₁ : z < c := lt_of_le_not_ge (le_iff_specializes.2 hcz)
    fun h ↦ hne (hcz.antisymm (le_iff_specializes.1 h)).eq
  have h₂ : c < genericPoint S := lt_of_le_not_ge
    (le_iff_specializes.2 ((genericPoint_spec S).specializes trivial))
    fun h ↦ hc (((genericPoint_spec S).specializes trivial).antisymm
      (le_iff_specializes.1 h)).eq.symm
  have h₃ := coheight_add_one_le h₁
  have h₄ := coheight_add_one_le h₂
  intro h
  rw [h] at h₃
  have h₅ : (2 : ℕ∞) ≤ coheight (genericPoint S) + 1 + 1 := by
    calc (2 : ℕ∞) = 0 + 1 + 1 := by norm_num
      _ ≤ coheight (genericPoint S) + 1 + 1 := by gcongr; exact bot_le
  have h₆ : coheight (genericPoint S) + 1 + 1 ≤ coheight c + 1 := by gcongr
  exact absurd (h₅.trans (h₆.trans h₃)) (by decide)


omit [IsIntegral X] in
/-- **Prime elements of a local ring define points of codimension one.** Let `X` be an integral
regular scheme and `V` an étale `X`-scheme. For a prime element `p` of the local ring `𝒪_{V,y}`,
the point of `V` defined by the prime ideal `(p)` lies over a point of `X` of codimension one: its
local ring is the localization of `𝒪_{V,y}` at `(p)`
(`AlgebraicGeometry.Scheme.isLocalization_stalkSpecializes`), of dimension the height of `(p)`,
which is one by Krull's principal ideal theorem. -/
lemma coheight_hom_fromSpecStalk_span (V : X.Etale) (y : V.left) {p : V.left.presheaf.stalk y}
    (hp : Prime p) :
    coheight (V.hom (V.left.fromSpecStalk y
      ⟨Ideal.span {p}, (Ideal.span_singleton_prime hp.ne_zero).2 hp⟩)) = 1 := by
  set q : PrimeSpectrum (V.left.presheaf.stalk y) :=
    ⟨Ideal.span {p}, (Ideal.span_singleton_prime hp.ne_zero).2 hp⟩
  have : (Ideal.span {p}).IsPrime := q.2
  rw [coheight_hom_apply]
  have h := ringKrullDim_stalk_eq_coheight (V.left.fromSpecStalk y q)
  let := (V.left.presheaf.stalkSpecializes (fromSpecStalk_specializes q)).hom.toAlgebra
  have : IsLocalization.AtPrime (V.left.presheaf.stalk (V.left.fromSpecStalk y q))
    (Ideal.span {p}) := isLocalization_stalkSpecializes_fromSpecStalk q
  have hd := IsLocalization.AtPrime.ringKrullDim_eq_height (Ideal.span {p})
    (V.left.presheaf.stalk (V.left.fromSpecStalk y q))
  have hh := Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
    (mem_nonZeroDivisors_of_ne_zero hp.ne_zero) hp.not_isUnit
  rw [hd, hh] at h
  exact_mod_cast h.symm

variable [IsLocallyNoetherian X]

/-- **Units of the local ring spread out.** Let `X` be an integral regular locally noetherian
scheme and `V` an étale `X`-scheme. If a function `f` on the generic fibre of `V` maps to a unit
`r` of `𝒪_{V,y}` in the local generic ring at `y`, then near `y` it is a unit of `𝒪_V`: `r` is the
germ of a unit on an affine irreducible neighbourhood `U` of `y`, which agrees with `f` on the
generic fibre of `U` by `AlgebraicGeometry.Scheme.Etale.injective_toLocalGenericRing`. -/
lemma exists_eq_of_toLocalGenericRing_eq (V : X.Etale) (y : V.left)
    (f : Γ(pullback V.hom X.fromSpecFunctionField, ⊤)) (r : (V.left.presheaf.stalk y)ˣ)
    (hr : toLocalGenericRing V y f = stalkToLocalGenericRing V y r) :
    ∃ (U : V.left.Opens) (_ : y ∈ U) (u : Γ(Etale.ofOpens V U |>.left, ⊤)ˣ),
      (pullback.fst (Etale.ofOpens V U).hom X.fromSpecFunctionField).appTop u.val =
        ((MorphismProperty.Over.pullback @Etale ⊤ X.fromSpecFunctionField).map
          (Etale.ofOpensι V U)).left.appTop f := by
  have : IsLocallyNoetherian ((Functor.fromPUnit X).obj V.right) := ‹IsLocallyNoetherian X›
  have : IsLocallyNoetherian V.left := LocallyOfFiniteType.isLocallyNoetherian V.hom
  have : IsReduced V.left := isReduced_of_isReduced_stalk _
  obtain ⟨W₀, hyW₀, hW₀⟩ := exists_opens_isPreirreducible y
  obtain ⟨U, hU, hyU, hUW₀, s, hs, hsr⟩ := exists_isAffineOpen_isUnit_germ_eq hyW₀ r
  have : IsIntegral (ofOpens V U).left := isIntegral_of_isPreirreducible hyU hW₀ hUW₀
  have : IsAffine (ofOpens V U).left := hU
  refine ⟨U, hyU, (hs.map U.topIso.inv.hom).unit, ?_⟩
  refine injective_toLocalGenericRing (ofOpens V U) ⟨y, hyU⟩ ?_
  have h₁ := congrArg (fun g ↦ g.hom f)
    (toLocalGenericRing_comp_localGenericRingMap (ofOpensι V U) ⟨y, hyU⟩)
  have h₂ := congrArg (fun g ↦ g.hom r.val)
    (stalkToLocalGenericRing_comp_localGenericRingMap (ofOpensι V U) ⟨y, hyU⟩)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h₁ h₂
  have h₃ : (ofOpens V U).left.presheaf.germ ⊤ ⟨y, hyU⟩ trivial (U.topIso.inv s) =
      (ofOpensι V U).left.stalkMap ⟨y, hyU⟩ r.val := by
    exact (germ_topIso_inv U s ⟨y, hyU⟩).trans ((congrArg (U.stalkIso ⟨y, hyU⟩).inv.hom hsr).trans
      (congrArg (fun g ↦ g.hom r.val) (Scheme.Opens.stalkIso_inv U ⟨y, hyU⟩)))
  refine ((toLocalGenericRing_fst_appTop (ofOpens V U) ⟨y, hyU⟩ (U.topIso.inv s)).trans ?_).trans h₁
  exact (congrArg _ h₃).trans (h₂.symm.trans (congrArg _ hr.symm))

omit [IsLocallyNoetherian X] in
/-- **Local algebraic Hartogs at a point.** Let `X` be an integral regular locally noetherian
scheme, `V` an étale `X`-scheme and `f` a unit on the generic fibre of `V` whose order vanishes
at every generalisation of `y`. Then `f` maps to a unit of `𝒪_{V,y}` in the local generic ring
at `y`. -/
lemma exists_toLocalGenericRing_eq_of_ord_eq_zero (V : X.Etale) (y : V.left)
    (f : Γ(pullback V.hom X.fromSpecFunctionField, ⊤)ˣ) (hf : ∀ w, w ⤳ y → ord V w f = 0) :
    ∃ r : (V.left.presheaf.stalk y)ˣ,
      toLocalGenericRing V y f = stalkToLocalGenericRing V y r := by
  have : IsRegular V.left := ⟨fun z ↦ inferInstance⟩
  have : UniqueFactorizationMonoid (V.left.presheaf.stalk y) :=
    IsRegular.uniqueFactorizationMonoid_stalk y
  let A := V.left.presheaf.stalk y
  let L := localGenericRing V y
  let : Algebra A L := (stalkToLocalGenericRing V y).hom.toAlgebra
  have : IsFractionRing A L := isFractionRing_localGenericRing V y
  let : Field L := IsFractionRing.toField A
  obtain ⟨a, b, hab, he⟩ := IsFractionRing.exists_reduced_fraction A (toLocalGenericRing V y f.val)
  have h₁ : stalkToLocalGenericRing V y a =
      toLocalGenericRing V y f * stalkToLocalGenericRing V y b :=
    (IsLocalization.mk'_eq_iff_eq_mul).1 he
  -- a prime divides `a` if and only if it divides `b`
  have key (p : A) (hp : Prime p) : p ∣ a ↔ p ∣ (b : A) := by
    let q : PrimeSpectrum A := ⟨Ideal.span {p}, (Ideal.span_singleton_prime hp.ne_zero).2 hp⟩
    have hw : V.left.fromSpecStalk y q ⤳ y := fromSpecStalk_specializes q
    have hcoh := coheight_hom_fromSpecStalk_span V y hp
    have hq := comap_stalkSpecializes_fromSpecStalk q
    have := isDiscreteValuationRing_stalk V hcoh
    let := (stalkToLocalGenericRing V (V.left.fromSpecStalk y q)).hom.toAlgebra
    have := isFractionRing_localGenericRing V (V.left.fromSpecStalk y q)
    have hord := hf _ hw
    rw [ord, ite_eq_left hcoh] at hord
    obtain ⟨r, hr⟩ := Ring.exists_eq_algebraMap_of_ordOf_eq_zero
      (Units.map (toLocalGenericRing V (V.left.fromSpecStalk y q)).hom.toMonoidHom f) hord
    let σ := (V.left.presheaf.stalkSpecializes hw).hom
    have h₂ := congrArg (localGenericRingSpecializes V hw).hom h₁
    have hc₁ := congrArg (fun g ↦ g.hom f.val)
      (toLocalGenericRing_comp_localGenericRingSpecializes V hw)
    have hc₂ (x : A) := congrArg (fun g ↦ g.hom x)
      (stalkToLocalGenericRing_comp_localGenericRingSpecializes V hw)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at hc₁ hc₂
    rw [map_mul, hc₂, hc₂, hc₁] at h₂
    have h₃ : σ a = r * σ b := by
      refine IsFractionRing.injective _
        (localGenericRing V (V.left.fromSpecStalk y q)) ?_
      rw [map_mul]
      exact h₂.trans (congrArg (· * _) hr.symm)
    have mem (x : A) : p ∣ x ↔ σ x ∈ IsLocalRing.maximalIdeal _ := by
      rw [← Ideal.mem_span_singleton]
      exact (Set.ext_iff.1 (congrArg SetLike.coe hq) x).symm
    rw [mem, mem, h₃]
    exact Ideal.unit_mul_mem_iff_mem _ r.isUnit
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [IsLocalization.mk'_zero] at he
    exact (f.isUnit.map (toLocalGenericRing V y).hom).ne_zero he.symm
  have hunit (x : A) (hx0 : x ≠ 0) (hx : ∀ p : A, Prime p → p ∣ x → False) : IsUnit x := by
    by_contra hxu
    obtain ⟨p, hp, hpx⟩ := WfDvdMonoid.exists_irreducible_factor hxu hx0
    exact hx p (UniqueFactorizationMonoid.irreducible_iff_prime.1 hp) hpx
  have ha : IsUnit a := hunit a ha0 fun p hp hpa ↦
    hp.not_isUnit (hab hpa ((key p hp).1 hpa))
  have hb : IsUnit (b : A) := hunit b (nonZeroDivisors.ne_zero b.2) fun p hp hpb ↦
    hp.not_isUnit (hab ((key p hp).2 hpb) hpb)
  refine ⟨ha.unit * hb.unit⁻¹, ?_⟩
  change _ = stalkToLocalGenericRing V y (a * ↑hb.unit⁻¹)
  rw [map_mul, h₁, mul_assoc, ← map_mul, IsUnit.mul_val_inv, map_one, mul_one]

omit [IsIntegral X] [IsRegular X] [IsLocallyNoetherian X] in
/-- The generic point of an integral scheme lies in the basic open of every nonzero function. -/
lemma _root_.AlgebraicGeometry.Scheme.genericPoint_mem_basicOpen {S : Scheme.{u}} [IsIntegral S]
    {a : Γ(S, ⊤)} (ha : a ≠ 0) : genericPoint S ∈ S.basicOpen a := by
  have hne : S.basicOpen a ≠ ⊥ := fun h ↦ ha ((basicOpen_eq_bot_iff a).1 h)
  obtain ⟨w, hw⟩ : (S.basicOpen a : Set S).Nonempty :=
    Set.nonempty_iff_ne_empty.2 fun h ↦ hne (Opens.ext (h.trans Opens.coe_bot.symm))
  exact ((genericPoint_spec S).mem_open_set_iff (S.basicOpen a).2).2 ⟨w, Set.mem_univ _, hw⟩

/-- **Local finiteness of divisors.** Let `X` be an integral regular locally noetherian scheme,
`V` an étale `X`-scheme and `f` a unit on the generic fibre of `V`. Near every point `y` of `V`,
`f` has nonzero order at only finitely many points. -/
lemma exists_opens_finite_ord_ne_zero (V : X.Etale) (y : V.left)
    (f : Γ(pullback V.hom X.fromSpecFunctionField, ⊤)ˣ) :
    ∃ U : V.left.Opens, y ∈ U ∧ {y' | y' ∈ U ∧ ord V y' f ≠ 0}.Finite := by
  have : IsLocallyNoetherian ((Functor.fromPUnit X).obj V.right) := ‹IsLocallyNoetherian X›
  have : IsLocallyNoetherian V.left := LocallyOfFiniteType.isLocallyNoetherian V.hom
  have : IsReduced V.left := isReduced_of_isReduced_stalk _
  let A := V.left.presheaf.stalk y
  let : Algebra A (localGenericRing V y) := (stalkToLocalGenericRing V y).hom.toAlgebra
  have : IsFractionRing A (localGenericRing V y) := isFractionRing_localGenericRing V y
  obtain ⟨⟨a₀, b₀⟩, hab⟩ := IsLocalization.mk'_surjective (nonZeroDivisors A)
    (toLocalGenericRing V y f.val)
  have h₁ : stalkToLocalGenericRing V y a₀ =
      toLocalGenericRing V y f * stalkToLocalGenericRing V y b₀ :=
    (IsLocalization.mk'_eq_iff_eq_mul).1 hab
  let : Field (localGenericRing V y) := IsFractionRing.toField A
  have ha₀ : a₀ ≠ 0 := by
    rintro rfl
    exact mul_ne_zero (f.isUnit.map (toLocalGenericRing V y).hom).ne_zero
      (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b₀.2)
      (h₁.symm.trans (map_zero (stalkToLocalGenericRing V y).hom))
  have hb₀ : (b₀ : A) ≠ 0 := nonZeroDivisors.ne_zero b₀.2
  -- an affine irreducible neighbourhood on which `a₀` and `b₀` are defined
  obtain ⟨W₀, hyW₀, hW₀⟩ := exists_opens_isPreirreducible y
  obtain ⟨U₁, -, hyU₁, hU₁, a₁, ha₁⟩ := exists_isAffineOpen_germ_eq hyW₀ a₀
  obtain ⟨U, hU, hyU, hUU₁, b, hb⟩ := exists_isAffineOpen_germ_eq hyU₁ (b₀ : A)
  let a := V.left.presheaf.map (homOfLE hUU₁).op a₁
  have ha : V.left.presheaf.germ U y hyU a = a₀ :=
    (V.left.presheaf.germ_res_apply _ _ _ _).trans ha₁
  have : IsIntegral (ofOpens V U).left := isIntegral_of_isPreirreducible hyU hW₀ (hUU₁.trans hU₁)
  have : IsAffine (ofOpens V U).left := hU
  let g : Γ(pullback (ofOpens V U).hom X.fromSpecFunctionField, ⊤)ˣ :=
    Units.map ((MorphismProperty.Over.pullback @Etale ⊤ X.fromSpecFunctionField).map
      (ofOpensι V U)).left.appTop.hom.toMonoidHom f
  -- `f b = a` on the generic fibre of `U`
  have heq : g.val * (pullback.fst (ofOpens V U).hom X.fromSpecFunctionField).appTop
      (U.topIso.inv b) =
      (pullback.fst (ofOpens V U).hom X.fromSpecFunctionField).appTop (U.topIso.inv a) := by
    refine injective_toLocalGenericRing (ofOpens V U) ⟨y, hyU⟩ ?_
    refine (map_mul _ _ _).trans ?_
    refine (congrArg₂ (· * ·) (toLocalGenericRing_map_ofOpensι V U ⟨y, hyU⟩ f.val)
      (toLocalGenericRing_fst_topIso_inv V U b ⟨y, hyU⟩)).trans ?_
    refine (map_mul _ _ _).symm.trans ?_
    refine Eq.trans ?_ (toLocalGenericRing_fst_topIso_inv V U a ⟨y, hyU⟩).symm
    refine congrArg (localGenericRingMap (ofOpensι V U) ⟨y, hyU⟩).hom ?_
    exact (congrArg (_ * ·) (congrArg (stalkToLocalGenericRing V y).hom hb)).trans
      (h₁.symm.trans (congrArg (stalkToLocalGenericRing V y).hom ha.symm))
  -- the closed set where `a` or `b` vanishes misses the generic point
  have hne (s : Γ(V.left, U)) (hs : V.left.presheaf.germ U y hyU s ≠ 0) :
      genericPoint (ofOpens V U).left ∈ (ofOpens V U).left.basicOpen (U.topIso.inv s) := by
    refine genericPoint_mem_basicOpen fun h0 ↦ hs ?_
    have := germ_topIso_inv U s ⟨y, hyU⟩
    rw [h0, map_zero] at this
    exact (U.stalkIso ⟨y, hyU⟩).commRingCatIsoToRingEquiv.symm.injective
      (this.symm.trans (map_zero _).symm)
  let Z : Set (ofOpens V U).left :=
    ((ofOpens V U).left.basicOpen (U.topIso.inv a) ⊓
      (ofOpens V U).left.basicOpen (U.topIso.inv b) : (ofOpens V U).left.Opens)ᶜ
  have hZ : IsClosed Z := Opens.isOpen _ |>.isClosed_compl
  have hξ : genericPoint (ofOpens V U).left ∉ Z := fun h ↦
    h ⟨hne a (ha ▸ ha₀), hne b (hb ▸ hb₀)⟩
  have : NoetherianSpace (ofOpens V U).left := @noetherianSpace_of_isAffineOpen _ U hU
    (IsLocallyNoetherian.component_noetherian ⟨U, hU⟩)
  have hfin := NoetherianSpace.finite_setOf_forall_specializes hZ hξ
  refine ⟨U, hyU, (hfin.image Subtype.val).subset ?_⟩
  rintro y' ⟨hy'U, hord⟩
  have hord' : ord (ofOpens V U) ⟨y', hy'U⟩ g ≠ 0 := fun h ↦
    hord ((ord_map (ofOpensι V U) ⟨y', hy'U⟩ f).symm.trans h)
  refine ⟨⟨y', hy'U⟩, ⟨fun hmem ↦ hord' ?_, fun c hc ↦ ?_⟩, rfl⟩
  · exact ord_eq_zero_of_mul_eq (ofOpens V U) _ g _ _ heq hmem.1 hmem.2
  · have hcoh : coheight ((ofOpens V U).hom ⟨y', hy'U⟩) = 1 := by
      by_contra h
      exact hord' (ord_of_coheight_ne_one _ h _)
    rw [coheight_hom_apply] at hcoh
    by_contra hne'
    push Not at hne'
    exact coheight_ne_one_of_specializes hc hne'.1 hne'.2 hcoh

omit [IsLocallyNoetherian X] in
/-- A function on `V` whose germ at a point `z` of codimension one is a uniformiser has order
`1` at `z`. -/
lemma ord_fst_appTop_eq_one (W : X.Etale) {z : W.left} (a : Γ(W.left, ⊤))
    (hirr : Irreducible (W.left.presheaf.germ ⊤ z trivial a)) (hcoh : coheight (W.hom z) = 1) :
    ord W z ((pullback.fst W.hom X.fromSpecFunctionField).appTop a) = 1 := by
  rw [ord, ite_eq_left hcoh, toLocalGenericRing_fst_appTop]
  have := isDiscreteValuationRing_stalk W hcoh
  let := (stalkToLocalGenericRing W z).hom.toAlgebra
  have := isFractionRing_localGenericRing W z
  exact Ring.ordOf_algebraMap_of_irreducible hirr

omit [IsLocallyNoetherian X] [IsIntegral X] in
/-- **Generalisations of codimension one are defined by prime elements.** Let `z ⤳ y` be a
generalisation in an étale `X`-scheme `V`, with `z` of codimension one, at which a prime element
`ρ` of `𝒪_{V,y}` vanishes. Then `z` is the point defined by the prime ideal `(ρ)`: the prime of
`𝒪_{V,y}` defined by `z` contains `(ρ)` and has height one. -/
lemma eq_fromSpecStalk_span (V : X.Etale) {z y : V.left} (h : z ⤳ y)
    {ρ : V.left.presheaf.stalk y} (hρ : Prime ρ)
    (hmem : V.left.presheaf.stalkSpecializes h ρ ∈ IsLocalRing.maximalIdeal _)
    (hz : coheight (V.hom z) = 1) :
    z = V.left.fromSpecStalk y ⟨Ideal.span {ρ}, (Ideal.span_singleton_prime hρ.ne_zero).2 hρ⟩ := by
  set q := (IsLocalRing.maximalIdeal (V.left.presheaf.stalk z)).comap
    (V.left.presheaf.stalkSpecializes h).hom
  have hq : V.left.fromSpecStalk y ⟨q, inferInstance⟩ = z := fromSpecStalk_comap_maximalIdeal h
  have hle : Ideal.span {ρ} ≤ q := (Ideal.span_singleton_le_iff_mem _).2 hmem
  let := (V.left.presheaf.stalkSpecializes h).hom.toAlgebra
  have := isLocalization_stalkSpecializes h
  have hd := IsLocalization.AtPrime.ringKrullDim_eq_height q (V.left.presheaf.stalk z)
  rw [ringKrullDim_stalk_eq_coheight, ← coheight_hom_apply, hz] at hd
  have hq1 : q.height = 1 := by exact_mod_cast hd.symm
  have : (Ideal.span {ρ}).IsPrime := (Ideal.span_singleton_prime hρ.ne_zero).2 hρ
  have heq : Ideal.span {ρ} = q := by
    by_contra hne
    have h₁ := Ideal.height_add_one_le_of_lt_of_isPrime (lt_of_le_of_ne hle hne)
    have h₂ := Ideal.one_le_height_span_singleton_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_of_ne_zero hρ.ne_zero)
    rw [hq1] at h₁
    have : (1 : ℕ∞) + 1 ≤ 1 := (add_le_add_left h₂ 1).trans' (by rw [add_comm]) |>.trans h₁
    exact absurd this (by decide)
  rw [← hq]
  exact congrArg _ (PrimeSpectrum.ext heq.symm)

omit [IsRegular X] [IsLocallyNoetherian X] in
/-- The order of vanishing of a finite product of powers of units. -/
lemma ord_prod_zpow (W : X.Etale) (z : W.left) {ι : Type*} (s : Finset ι)
    (g : ι → Γ(pullback W.hom X.fromSpecFunctionField, ⊤)ˣ) (n : ι → ℤ) :
    ord W z ↑(∏ i ∈ s, g i ^ n i) = ∑ i ∈ s, n i * ord W z (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using ord_one W z
  | insert i s hi ih => rw [Finset.prod_insert hi, ord_mul, ord_zpow, ih, Finset.sum_insert hi]

omit [IsRegular X] [IsLocallyNoetherian X] in
/-- A function on an open `U` of `V` which is invertible at the points of `U` over the generic
point of `X` is invertible on the generic fibre of `U`. -/
lemma isUnit_fst_appTop_topIso_inv (V : X.Etale) (U : V.left.Opens) (a : Γ(V.left, U))
    (h : ∀ z : U, V.hom z.1 = genericPoint X → IsUnit (V.left.presheaf.germ U z z.2 a)) :
    IsUnit ((pullback.fst (ofOpens V U).hom X.fromSpecFunctionField).appTop (U.topIso.inv a)) := by
  refine isUnit_of_basicOpen_eq_top _ ?_
  rw [← Scheme.preimage_basicOpen_top, eq_top_iff]
  intro p _
  change pullback.fst (ofOpens V U).hom X.fromSpecFunctionField p ∈
    (ofOpens V U).left.basicOpen (U.topIso.inv a)
  set z := pullback.fst (ofOpens V U).hom X.fromSpecFunctionField p
  have hz : V.hom z.1 = genericPoint X := by
    have e := congrArg (fun g ↦ g p) (pullback.condition (f := (ofOpens V U).hom)
      (g := X.fromSpecFunctionField))
    have : Subsingleton (Spec X.functionField) :=
      inferInstanceAs (Subsingleton (PrimeSpectrum X.functionField))
    have hp : pullback.snd (ofOpens V U).hom X.fromSpecFunctionField p =
        IsLocalRing.closedPoint X.functionField := Subsingleton.elim _ _
    exact e.trans ((congrArg (X.fromSpecStalk (genericPoint X)) hp).trans fromSpecStalk_closedPoint)
  rw [Scheme.mem_basicOpen_top]
  have h₁ := (h z hz).map (U.stalkIso z).inv.hom
  rw [← germ_topIso_inv] at h₁
  exact h₁

omit [IsLocallyNoetherian X] [IsIntegral X] in
/-- A generalisation of `y` at which a nonzero element of `𝒪_{V,y}` vanishes is not a maximal
point: the prime of `𝒪_{V,y}` it defines is nonzero. -/
lemma coheight_ne_zero_of_mem (V : X.Etale) {g y : V.left} (h : g ⤳ y)
    {ρ : V.left.presheaf.stalk y} (hρ : ρ ≠ 0)
    (hmem : V.left.presheaf.stalkSpecializes h ρ ∈ IsLocalRing.maximalIdeal _) :
    coheight g ≠ 0 := by
  set q := (IsLocalRing.maximalIdeal (V.left.presheaf.stalk g)).comap
    (V.left.presheaf.stalkSpecializes h).hom
  let := (V.left.presheaf.stalkSpecializes h).hom.toAlgebra
  have := isLocalization_stalkSpecializes h
  have hd := IsLocalization.AtPrime.ringKrullDim_eq_height q (V.left.presheaf.stalk g)
  rw [ringKrullDim_stalk_eq_coheight] at hd
  intro h0
  rw [h0] at hd
  have hq : q.height = 0 := by exact_mod_cast hd.symm
  have h₁ := Ideal.height_mono ((Ideal.span_singleton_le_iff_mem q).2 hmem)
  have h₂ := Ideal.one_le_height_span_singleton_of_mem_nonZeroDivisors
    (mem_nonZeroDivisors_of_ne_zero hρ)
  rw [hq] at h₁
  exact absurd (h₂.trans h₁) (by decide)

omit [IsLocallyNoetherian X] [IsIntegral X] in
/-- The germ of a prime element `ρ` of `𝒪_{V,y}` at the point defined by `(ρ)` is a uniformiser
of the discrete valuation ring `𝒪_{V,w}`, the localization of `𝒪_{V,y}` at `(ρ)`. -/
lemma irreducible_stalkSpecializes (V : X.Etale) {w y : V.left} (h : w ⤳ y)
    {ρ : V.left.presheaf.stalk y} (hρ : Prime ρ)
    (hw : w = V.left.fromSpecStalk y
      ⟨Ideal.span {ρ}, (Ideal.span_singleton_prime hρ.ne_zero).2 hρ⟩) :
    Irreducible (V.left.presheaf.stalkSpecializes h ρ) := by
  subst hw
  have : (Ideal.span {ρ}).IsPrime := (Ideal.span_singleton_prime hρ.ne_zero).2 hρ
  have := isDiscreteValuationRing_stalk V (coheight_hom_fromSpecStalk_span V y hρ)
  let := (V.left.presheaf.stalkSpecializes h).hom.toAlgebra
  have := isLocalization_stalkSpecializes_fromSpecStalk (X := V.left)
    ⟨Ideal.span {ρ}, (Ideal.span_singleton_prime hρ.ne_zero).2 hρ⟩
  rw [IsDiscreteValuationRing.irreducible_iff_uniformizer,
    ← IsLocalization.AtPrime.map_eq_maximalIdeal (Ideal.span {ρ}), Ideal.map_span,
    Set.image_singleton]
  rfl

omit [IsIntegral X] [IsRegular X] [IsLocallyNoetherian X] in
/-- A point of an open subscheme `U` lies in the basic open of a section over `U`, transported to
`U`, if and only if it lies in the basic open of the section. -/
lemma mem_basicOpen_topIso_inv {S : Scheme.{u}} (U : S.Opens) (a : Γ(S, U)) (z : U) :
    z ∈ U.toScheme.basicOpen (U.topIso.inv a) ↔ z.1 ∈ S.basicOpen a := by
  rw [← Scheme.Opens.ι_image_basicOpen_topIso_inv U a]
  exact ⟨fun h ↦ ⟨z, h, rfl⟩, fun ⟨z', hz', e⟩ ↦ by rwa [← Subtype.ext e]⟩

omit [IsLocallyNoetherian X] in
/-- A section over an open `U` of `V` whose germ at a point `z` of codimension one is a
uniformiser has order `1` at `z` on the generic fibre of `U`. -/
lemma ord_fst_topIso_inv_eq_one (V : X.Etale) (U : V.left.Opens) (a : Γ(V.left, U)) (z : U)
    (hirr : Irreducible (V.left.presheaf.germ U z z.2 a)) (hcoh : coheight (V.hom z.1) = 1) :
    ord (ofOpens V U) z
      ((pullback.fst (ofOpens V U).hom X.fromSpecFunctionField).appTop (U.topIso.inv a)) = 1 := by
  have h := (MulEquiv.irreducible_iff
    (U.stalkIso z).symm.commRingCatIsoToRingEquiv.toMulEquiv).2 hirr
  change Irreducible ((U.stalkIso z).inv _) at h
  rw [← germ_topIso_inv] at h
  exact ord_fst_appTop_eq_one (ofOpens V U) _ h hcoh

omit [IsRegular X] [IsIntegral X] in
/-- **Points over `x` near `y` generalise `y`.** For a point `x` of `X`, a point `y` of an étale
`X`-scheme `V` has an open neighbourhood, inside any given one, all of whose points over `x`
generalise `y`: remove the irreducible components of the preimage of the closure of `x` not
containing `y`, and use that the fibres of `V ⟶ X` are discrete. -/
lemma exists_opens_specializes_of_hom_eq (V : X.Etale) (y : V.left) (x : X) {N : V.left.Opens}
    (hyN : y ∈ N) :
    ∃ U : V.left.Opens, y ∈ U ∧ U ≤ N ∧ ∀ z ∈ U, V.hom z = x → z ⤳ y := by
  have : IsLocallyNoetherian ((Functor.fromPUnit X).obj V.right) := ‹IsLocallyNoetherian X›
  have : IsLocallyNoetherian V.left := LocallyOfFiniteType.isLocallyNoetherian V.hom
  obtain ⟨_, ⟨U₀, hU₀, rfl⟩, hyU₀, hU₀N⟩ :=
    V.left.isBasis_affineOpens.exists_subset_of_mem_open hyN N.2
  have : NoetherianSpace U₀ := @noetherianSpace_of_isAffineOpen _ U₀ hU₀
    (IsLocallyNoetherian.component_noetherian ⟨U₀, hU₀⟩)
  have : QuasiSober U₀ := inferInstanceAs (QuasiSober (Scheme.Opens.toScheme (X := V.left) U₀))
  let Z : Set U₀ := (fun z : U₀ ↦ V.hom z.1) ⁻¹' closure {x}
  have hZ : IsClosed Z := isClosed_closure.preimage (V.hom.continuous.comp continuous_subtype_val)
  obtain ⟨O, hO, hyO, hOZ⟩ := NoetherianSpace.exists_isOpen_forall_exists_specializes hZ
    (⟨y, hyU₀⟩ : U₀)
  refine ⟨⟨Subtype.val '' O, U₀.2.isOpenMap_subtype_val O hO⟩, ⟨_, hyO, rfl⟩,
    fun _ ⟨z, _, hz⟩ ↦ hz ▸ hU₀N z.2, ?_⟩
  rintro _ ⟨z, hzO, rfl⟩ hzx
  obtain ⟨g, hgZ, hgz, hgy⟩ := hOZ z hzO (by
    change V.hom z.1 ∈ closure {x}
    rw [hzx]
    exact subset_closure rfl)
  have hgz' := hgz.map continuous_subtype_val
  have hg : V.hom g.1 = V.hom z.1 :=
    ((hgz'.map V.hom.continuous).antisymm (hzx ▸ specializes_iff_mem_closure.2 hgZ)).eq
  rw [← V.hom.eq_of_specializes_of_apply_eq hgz' hg]
  exact hgy.map continuous_subtype_val

omit [IsRegular X] [IsIntegral X] in
/-- **Finiteness of fibres over codimension one points.** On an irreducible affine open `U` of an
étale `X`-scheme, the points over a point `x` of codimension one are finitely many: they are
generic points of irreducible components of the preimage of the closure of `x`. -/
lemma finite_setOf_hom_eq (V : X.Etale) (U : V.left.Opens) (hU : IsAffineOpen U)
    (hirr : IsPreirreducible (U : Set V.left)) {x : X} (hx : coheight x = 1) :
    {w | w ∈ U ∧ V.hom w = x}.Finite := by
  have : IsLocallyNoetherian ((Functor.fromPUnit X).obj V.right) := ‹IsLocallyNoetherian X›
  have : IsLocallyNoetherian V.left := LocallyOfFiniteType.isLocallyNoetherian V.hom
  rcases isEmpty_or_nonempty U with hU0 | hU0
  · exact Set.finite_empty.subset fun w hw ↦ hU0.elim ⟨w, hw.1⟩
  have : NoetherianSpace (Scheme.Opens.toScheme (X := V.left) U) :=
    @noetherianSpace_of_isAffineOpen _ U hU
    (IsLocallyNoetherian.component_noetherian ⟨U, hU⟩)
  have : IrreducibleSpace (Scheme.Opens.toScheme (X := V.left) U) := Subtype.irreducibleSpace
    ⟨Set.nonempty_coe_sort.1 hU0, hirr⟩
  let Z : Set (Scheme.Opens.toScheme (X := V.left) U) := (fun z : U ↦ V.hom z.1) ⁻¹' closure {x}
  have hZ : IsClosed Z := isClosed_closure.preimage (V.hom.continuous.comp continuous_subtype_val)
  have hcoh (z : (Scheme.Opens.toScheme (X := V.left) U)) : coheight z = coheight (V.hom z.1) := by
    rw [coheight_hom_apply, ← coheight_eq_of_isOpenImmersion U.ι]
    rfl
  have hξ : genericPoint (Scheme.Opens.toScheme (X := V.left) U) ∉ Z := by
    intro hξ
    have hmax : IsMax (V.hom (genericPoint (Scheme.Opens.toScheme (X := V.left) U)).1) := by
      rw [← Order.coheight_eq_zero, ← hcoh, Order.coheight_eq_zero]
      intro b _
      exact le_iff_specializes.2
        ((genericPoint_spec (Scheme.Opens.toScheme (X := V.left) U)).specializes trivial)
    have hle : V.hom (genericPoint (Scheme.Opens.toScheme (X := V.left) U)).1 ≤ x :=
      le_iff_specializes.2 (specializes_iff_mem_closure.2 hξ)
    have heq : x = V.hom (genericPoint (Scheme.Opens.toScheme (X := V.left) U)).1 :=
      ((le_iff_specializes.1 (hmax hle)).antisymm (le_iff_specializes.1 hle)).eq.symm
    rw [heq, Order.coheight_eq_zero.2 hmax] at hx
    exact absurd hx (by decide)
  refine ((NoetherianSpace.finite_setOf_forall_specializes hZ hξ).image Subtype.val).subset ?_
  rintro w ⟨hwU, hwx⟩
  refine ⟨⟨w, hwU⟩, ⟨?_, fun c hc ↦ ?_⟩, rfl⟩
  · change V.hom w ∈ closure {x}
    rw [hwx]
    exact subset_closure rfl
  · by_contra hne
    push Not at hne
    refine coheight_ne_one_of_specializes hc hne.1 hne.2 ?_
    rw [hcoh]
    exact hwx ▸ hx

/-- **Weil divisors supported over a codimension one point are locally principal.** Let `X` be an
integral regular locally noetherian scheme, `x` a point of `X` of codimension one, `V` an étale
`X`-scheme and `e` an integer-valued function on the points of `V` vanishing outside the fibre
over `x`. Near every point `y` of `V` there is a unit on the generic fibre whose order is `e`. -/
lemma exists_ord_eq_of_forall_ne (V : X.Etale) (y : V.left) {x : X} (hx : coheight x = 1)
    (e : V.left → ℤ) (he : ∀ z, V.hom z ≠ x → e z = 0) :
    ∃ (U : V.left.Opens) (_ : y ∈ U)
      (f : Γ(pullback (ofOpens V U).hom X.fromSpecFunctionField, ⊤)ˣ),
      ∀ z : U, ord (ofOpens V U) z f = e z := by
  classical
  have : IsLocallyNoetherian ((Functor.fromPUnit X).obj V.right) := ‹IsLocallyNoetherian X›
  have : IsLocallyNoetherian V.left := LocallyOfFiniteType.isLocallyNoetherian V.hom
  have : IsRegular V.left := ⟨fun z ↦ inferInstance⟩
  have : UniqueFactorizationMonoid (V.left.presheaf.stalk y) :=
    IsRegular.uniqueFactorizationMonoid_stalk y
  -- `x` does not specialise to the generic point
  have hxη : ¬ x ⤳ genericPoint X := fun h ↦ by
    have hmax : IsMax (genericPoint X) := fun b _ ↦
      le_iff_specializes.2 ((genericPoint_spec X).specializes trivial)
    have : x = genericPoint X := (h.antisymm ((genericPoint_spec X).specializes trivial)).eq
    rw [this, Order.coheight_eq_zero.2 hmax] at hx
    exact absurd hx (by decide)
  -- near `y`, the points over `x` generalise `y` and are finitely many
  obtain ⟨W₀, hyW₀, hW₀⟩ := exists_opens_isPreirreducible y
  obtain ⟨_, ⟨U₀, hU₀, rfl⟩, hyU₀, hU₀W₀⟩ :=
    V.left.isBasis_affineOpens.exists_subset_of_mem_open hyW₀ W₀.2
  obtain ⟨U₁, hyU₁, hU₁U₀, hgen⟩ := exists_opens_specializes_of_hom_eq V y x (N := U₀) hyU₀
  have hF : {w | w ∈ U₁ ∧ V.hom w = x}.Finite :=
    (finite_setOf_hom_eq V U₀ hU₀ (hW₀.open_subset U₀.2 hU₀W₀) hx).subset
      fun w hw ↦ ⟨hU₁U₀ hw.1, hw.2⟩
  set F := hF.toFinset
  have hFmem {w : V.left} (hw : w ∈ F) : w ∈ U₁ ∧ V.hom w = x := (Set.Finite.mem_toFinset hF).1 hw
  -- each of them is defined by a prime element of `𝒪_{V,y}`
  have hρ (w : V.left) (hw : w ∈ F) : ∃ (ρ : V.left.presheaf.stalk y) (hρ : Prime ρ),
      w = V.left.fromSpecStalk y
        ⟨Ideal.span {ρ}, (Ideal.span_singleton_prime hρ.ne_zero).2 hρ⟩ := by
    have hwy := hgen w (hFmem hw).1 (hFmem hw).2
    have hcoh : coheight (V.hom w) = 1 := (hFmem hw).2 ▸ hx
    set q := (IsLocalRing.maximalIdeal (V.left.presheaf.stalk w)).comap
      (V.left.presheaf.stalkSpecializes hwy).hom
    have hq0 : q ≠ ⊥ := by
      intro h0
      let := (V.left.presheaf.stalkSpecializes hwy).hom.toAlgebra
      have := isLocalization_stalkSpecializes hwy
      have hd := IsLocalization.AtPrime.ringKrullDim_eq_height q (V.left.presheaf.stalk w)
      rw [ringKrullDim_stalk_eq_coheight, ← coheight_hom_apply, hcoh] at hd
      rw [h0, Ideal.height_bot] at hd
      exact absurd hd (by decide)
    obtain ⟨ρ, hρq, hρ⟩ := Ideal.IsPrime.exists_mem_prime_of_ne_bot inferInstance hq0
    exact ⟨ρ, hρ, eq_fromSpecStalk_span V hwy hρ hρq hcoh⟩
  choose! ρ hρp hρw using hρ
  -- sections extending the `ρ_w`
  have hsec (w : V.left) (_ : w ∈ F) : ∃ (Uw : V.left.Opens) (_ : IsAffineOpen Uw) (hyUw : y ∈ Uw)
      (_ : Uw ≤ U₁) (s : Γ(V.left, Uw)), V.left.presheaf.germ Uw y hyUw s = ρ w :=
    exists_isAffineOpen_germ_eq hyU₁ (ρ w)
  choose! Uw hUw hyUw hUwU₁ s hs using hsec
  have hgerm (w : V.left) (hw : w ∈ F) {g : V.left} (hg : g ∈ Uw w) (hgy : g ⤳ y) :
      V.left.presheaf.germ (Uw w) g hg (s w) = V.left.presheaf.stalkSpecializes hgy (ρ w) := by
    rw [← hs w hw]
    exact (congrArg (fun φ ↦ φ.hom (s w))
      (V.left.presheaf.germ_stalkSpecializes (hyUw w hw) hgy)).symm
  -- neighbourhoods on which `ρ_w` vanishes only at specialisations of generalisations of `y`
  have hnbhd (w : V.left) (hw : w ∈ F) : ∃ O : V.left.Opens, y ∈ O ∧ O ≤ Uw w ∧
      ∀ z ∈ O, z ∉ V.left.basicOpen (s w) → ∃ g, ∃ (hg : g ∈ Uw w) (hgy : g ⤳ y), g ⤳ z ∧
        V.left.presheaf.stalkSpecializes hgy (ρ w) ∈ IsLocalRing.maximalIdeal _ := by
    have : NoetherianSpace (Uw w) := @noetherianSpace_of_isAffineOpen _ _ (hUw w hw)
      (IsLocallyNoetherian.component_noetherian ⟨_, hUw w hw⟩)
    have : QuasiSober (Uw w) := inferInstanceAs (QuasiSober (Scheme.Opens.toScheme (X := V.left)
      (Uw w)))
    let Z : Set (Uw w) := {z | z.1 ∉ V.left.basicOpen (s w)}
    have hZ : IsClosed Z :=
      ((V.left.basicOpen (s w)).2.preimage continuous_subtype_val).isClosed_compl
    obtain ⟨O, hO, hyO, hOZ⟩ :=
      NoetherianSpace.exists_isOpen_forall_exists_specializes hZ (⟨y, hyUw w hw⟩ : Uw w)
    refine ⟨⟨Subtype.val '' O, (Uw w).2.isOpenMap_subtype_val O hO⟩, ⟨_, hyO, rfl⟩,
      fun _ ⟨z, _, hz⟩ ↦ hz ▸ z.2, ?_⟩
    rintro _ ⟨z, hzO, rfl⟩ hz
    obtain ⟨g, hgZ, hgz, hgy⟩ := hOZ z hzO hz
    have hgy' := hgy.map continuous_subtype_val
    refine ⟨g.1, g.2, hgy', hgz.map continuous_subtype_val, ?_⟩
    rw [← hgerm w hw g.2 hgy', IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact fun h ↦ hgZ ((V.left.mem_basicOpen _ _ _).2 h)
  choose! O hyO hOUw hOZ using hnbhd
  let U : V.left.Opens := U₁ ⊓ F.inf O
  have hUO (w : V.left) (hw : w ∈ F) : U ≤ O w := fun z hz ↦ by
    have := hz.2
    rw [Opens.coe_finset_inf, Finset.inf_set_eq_iInter] at this
    exact Set.mem_iInter₂.1 this w hw
  have hyU : y ∈ U := ⟨hyU₁, by
    rw [Opens.coe_finset_inf, Finset.inf_set_eq_iInter]
    exact Set.mem_iInter₂.2 fun w hw ↦ hyO w hw⟩
  have hUUw (w : V.left) (hw : w ∈ F) : U ≤ Uw w := (hUO w hw).trans (hOUw w hw)
  -- the restrictions of the `ρ_w` to `U`
  let r (w : V.left) : Γ(V.left, U) :=
    if hw : w ∈ F then V.left.presheaf.map (homOfLE (hUUw w hw)).op (s w) else 1
  have hr (w : V.left) (hw : w ∈ F) (z : U) :
      V.left.presheaf.germ U z z.2 (r w) = V.left.presheaf.germ (Uw w) z (hUUw w hw z.2) (s w) := by
    simp only [r, dite_eq_left hw]
    exact V.left.presheaf.germ_res_apply _ _ _ _
  -- a point of `U` at which `ρ_w` vanishes is a specialisation of a generalisation `g` of `y`
  -- at which `ρ_w` vanishes
  have hvan (w : V.left) (hw : w ∈ F) (z : U)
      (hz : ¬ IsUnit (V.left.presheaf.germ U z z.2 (r w))) : ∃ g, ∃ (hgy : g ⤳ y), g ⤳ z ∧
        V.left.presheaf.stalkSpecializes hgy (ρ w) ∈ IsLocalRing.maximalIdeal _ := by
    rw [hr w hw] at hz
    obtain ⟨g, -, hgy, hgz, hmem⟩ := hOZ w hw z (hUO w hw z.2)
      fun h ↦ hz ((V.left.mem_basicOpen _ _ _).1 h)
    exact ⟨g, hgy, hgz, hmem⟩
  -- the `ρ_w` are units on the generic fibre of `U`
  have hunit (w : V.left) :
      IsUnit ((pullback.fst (ofOpens V U).hom X.fromSpecFunctionField).appTop
        (U.topIso.inv (r w))) := by
    by_cases hw : w ∈ F
    · refine isUnit_fst_appTop_topIso_inv V U _ fun z hzη ↦ ?_
      by_contra hnu
      obtain ⟨g, hgy, hgz, hmem⟩ := hvan w hw z hnu
      have hwg : w ⤳ g := by
        rw [hρw w hw, ← fromSpecStalk_comap_maximalIdeal hgy]
        refine ((PrimeSpectrum.le_iff_specializes _ _).1 ?_).map
          (V.left.fromSpecStalk y).continuous
        exact (Ideal.span_singleton_le_iff_mem _).2 hmem
      have := (hwg.map V.hom.continuous).trans (hgz.map V.hom.continuous)
      rw [(hFmem hw).2, hzη] at this
      exact hxη this
    · simp only [r, dite_eq_right hw, map_one]
      exact isUnit_one
  -- the order of `ρ_w` at a point `z` of `U` is `1` if `z = w` and `0` otherwise
  have hord (w : V.left) (hw : w ∈ F) (z : U) :
      ord (ofOpens V U) z (hunit w).unit = if z.1 = w then 1 else 0 := by
    split_ifs with hzw
    · have hwy := hgen w (hFmem hw).1 (hFmem hw).2
      have hzy : z.1 ⤳ y := hzw ▸ hwy
      refine ord_fst_topIso_inv_eq_one V U _ z ?_ (by rw [hzw, (hFmem hw).2]; exact hx)
      rw [hr w hw, hgerm w hw _ hzy]
      exact irreducible_stalkSpecializes V hzy (hρp w hw) (hzw.trans (hρw w hw))
    · by_cases hu : IsUnit (V.left.presheaf.germ U z z.2 (r w))
      · refine ord_eq_zero_of_mul_eq (ofOpens V U) z _ (U.topIso.inv (r w)) 1 ?_ ?_ ?_
        · rw [map_one, mul_one, IsUnit.unit_spec]
        · exact (mem_basicOpen_topIso_inv U (r w) z).2 ((V.left.mem_basicOpen _ _ _).2 hu)
        · rw [Scheme.basicOpen_one]
          trivial
      · by_cases hcoh : coheight (V.hom z.1) = 1
        · exfalso
          obtain ⟨g, hgy, hgz, hmem⟩ := hvan w hw z hu
          have hgz' : g = z.1 := by
            by_contra hne
            have hlt : z.1 < g := lt_of_le_not_ge (le_iff_specializes.2 hgz)
              fun h ↦ hne (hgz.antisymm (le_iff_specializes.1 h)).eq
            have := coheight_add_one_le hlt
            rw [show coheight z.1 = 1 from (coheight_hom_apply V z.1).symm.trans hcoh] at this
            refine coheight_ne_zero_of_mem V hgy (hρp w hw).ne_zero hmem ?_
            by_contra h0
            have h1 : 1 ≤ coheight g := Order.one_le_iff_ne_zero.2 h0
            have : (1 : ℕ∞) + 1 ≤ 1 :=
              (add_le_add_left h1 1).trans' (by rw [add_comm]) |>.trans this
            exact absurd this (by decide)
          subst hgz'
          exact hzw ((eq_fromSpecStalk_span V hgy (hρp w hw) hmem hcoh).trans (hρw w hw).symm)
        · exact ord_of_coheight_ne_one (ofOpens V U) (y := z) hcoh _
  refine ⟨U, hyU, ∏ w ∈ F, (hunit w).unit ^ e w, fun z ↦ ?_⟩
  rw [ord_prod_zpow, Finset.sum_congr rfl fun w hw ↦ by rw [hord w hw]]
  simp only [mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq]
  split_ifs with hzF
  · rfl
  · exact (he _ fun hzx ↦
      hzF ((Set.Finite.mem_toFinset hF).2 ⟨(inf_le_left : U ≤ U₁) z.2, hzx⟩)).symm

end Etale

end AlgebraicGeometry.Scheme
