/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PrincipalOpenCechSubsetInsertion
import Mathlib.Order.Interval.Finset.Fin

/-! # One coordinate of the horizontal Čech differential

Source: Stacks Project, Tags 08C1, 08C0, and 01FG.
(blueprint: lem-sc-principal-open-cech-subset-horizontal-face-coordinate).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry
attribute [local instance] Functor.additive_of_preserves_binary_products
attribute [local instance] Classical.propDecidable

private theorem alternatingRow_d_apply {X : Scheme.{u}} {r : ℕ}
    (U : Fin r → X.Opens)
    (G : X.Opensᵒᵖ ⥤ ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤)))
    (p : ℕ)
    (s : alternatingCechTerms U G p) (t : Fin (p + 2) ↪o Fin r) :
    (alternatingCechDifferential U G p).hom s t =
      ∑ j : Fin (p + 2), (-1 : ℤ) ^ j.val •
        (G.map (homOfLE (alternatingCechIntersection_face_le U p t j)).op).hom
          (s ((Fin.succAboveOrderEmb j).trans t)) := by
  change (∀ q : Fin (p + 1) ↪o Fin r, G.obj (op (alternatingCechIntersection U q))) at s
  change ((∑ j : Fin (p + 2), (-1 : ℤ) ^ j.val •
    (G.map (homOfLE (alternatingCechIntersection_face_le U p t j)).op).hom.comp
      (LinearMap.proj ((Fin.succAboveOrderEmb j).trans t))) s) = _
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply]
  rfl

private theorem eraseEnumeration (r p : ℕ)
    (T : {T : Finset (Fin r) // T.card = (p + 1) + 1}) (j : Fin (p + 2)) :
    (T.val.orderEmbOfFin T.property) ∘ j.succAbove =
      (T.val.erase (T.val.orderEmbOfFin T.property j)).orderEmbOfFin (by
        rw [Finset.card_erase_of_mem (T.val.orderEmbOfFin_mem T.property j), T.property]
        omega) := by
  apply Finset.orderEmbOfFin_unique
  · intro i
    apply Finset.mem_erase.mpr
    constructor
    · intro h
      exact Fin.succAbove_ne j i ((T.val.orderEmbOfFin T.property).injective h)
    · exact T.val.orderEmbOfFin_mem T.property (j.succAbove i)
  · exact (T.val.orderEmbOfFin T.property).strictMono.comp (Fin.strictMono_succAbove j)

private theorem countBefore (r p : ℕ)
    (T : {T : Finset (Fin r) // T.card = p + 1}) (j : Fin (p + 1)) :
    (T.val.filter (fun i ↦ i < T.val.orderEmbOfFin T.property j)).card = j.val := by
  classical
  let t := T.val.orderEmbOfFin T.property
  change (T.val.filter (fun i ↦ i < t j)).card = j.val
  conv_lhs => arg 1; arg 2; rw [← Finset.image_orderEmbOfFin_univ T.val T.property]
  rw [Finset.filter_image]
  have hfilter : (Finset.univ.filter (fun i ↦
      T.val.orderEmbOfFin T.property i < T.val.orderEmbOfFin T.property j)) =
      Finset.Iio j := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iio]
    exact (T.val.orderEmbOfFin T.property).lt_iff_lt
  rw [hfilter, Finset.card_image_of_injective _ (T.val.orderEmbOfFin T.property).injective,
    Fin.card_Iio]

private theorem transport_restriction
    (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A)
    (M : (Spec (.of A)).Modules)
    (S T : {S : Finset (Fin r) // S.Nonempty})
    (hle : principalSubsetOpen A r f T.val ≤ principalSubsetOpen A r f S.val)
    (hW : alternatingCechIntersection
        (fun i ↦ (principalSubsetUnion A r f).ι ⁻¹ᵁ PrimeSpectrum.basicOpen (f i))
        (principalSubsetTuple r T) ≤ alternatingCechIntersection
        (fun i ↦ (principalSubsetUnion A r f).ι ⁻¹ᵁ PrimeSpectrum.basicOpen (f i))
        (principalSubsetTuple r S))
    (x : (modulesSpecToSheaf.obj M).obj.obj (op (principalSubsetOpen A r f S.val))) :
    (principalSubsetSectionTransport A r f M T).hom
        ((modulesSpecToSheaf.obj M).obj.map (homOfLE hle).op x) =
      ((SheafOfModules.overFunctor.{u} (moduleRings (Spec (.of A)).toRingedSpace)
        (principalSubsetUnion A r f) ⋙
          (Scheme.Modules.overEquiv (principalSubsetUnion A r f)).functor).obj M).presheaf.map
        (homOfLE hW).op ((principalSubsetSectionTransport A r f M S).hom x) := by
  let V := principalSubsetUnion A r f
  let WS := alternatingCechIntersection
    (fun i ↦ V.ι ⁻¹ᵁ PrimeSpectrum.basicOpen (f i)) (principalSubsetTuple r S)
  let WT := alternatingCechIntersection
    (fun i ↦ V.ι ⁻¹ᵁ PrimeSpectrum.basicOpen (f i)) (principalSubsetTuple r T)
  let e := (Scheme.Modules.overFunctorEquiv V).inv.app M
  have hS : V.ι ''ᵁ WS = principalSubsetOpen A r f S.val := by
    dsimp only [WS, V]
    rw [principalSubsetIntersection, V.ι.image_preimage_eq_opensRange_inf,
      Scheme.Opens.opensRange_ι, inf_eq_right.mpr (principalSubsetOpen_le A r f S)]
  have hT : V.ι ''ᵁ WT = principalSubsetOpen A r f T.val := by
    dsimp only [WT, V]
    rw [principalSubsetIntersection, V.ι.image_preimage_eq_opensRange_inf,
      Scheme.Opens.opensRange_ι, inf_eq_right.mpr (principalSubsetOpen_le A r f T)]
  have he := congrArg (fun z ↦ z (M.presheaf.map (eqToHom hS).op x))
    (e.mapPresheaf.naturality (homOfLE hW).op)
  refine Eq.trans ?_ he
  change (e.app WT)
      (M.presheaf.map (eqToHom hT).op (M.presheaf.map (homOfLE hle).op x)) =
    (e.app WT) (M.presheaf.map (homOfLE (Scheme.Hom.image_mono V.ι hW)).op
      (M.presheaf.map (eqToHom hS).op x))
  apply congrArg (e.app WT)
  rw [← Functor.map_comp_apply, ← Functor.map_comp_apply]
  congr 1

private theorem transport_restriction_cast
    (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A)
    (M N : (Spec (.of A)).Modules) (φ : M ⟶ N) (ψ : N ⟶ M) (hφψ : φ ≫ ψ = 𝟙 M)
    (S T : {S : Finset (Fin r) // S.Nonempty})
    (hle : principalSubsetOpen A r f T.val ≤ principalSubsetOpen A r f S.val)
    (hW : alternatingCechIntersection
        (fun i ↦ (principalSubsetUnion A r f).ι ⁻¹ᵁ PrimeSpectrum.basicOpen (f i))
        (principalSubsetTuple r T) ≤ alternatingCechIntersection
        (fun i ↦ (principalSubsetUnion A r f).ι ⁻¹ᵁ PrimeSpectrum.basicOpen (f i))
        (principalSubsetTuple r S))
    (x : (modulesSpecToSheaf.obj M).obj.obj (op (principalSubsetOpen A r f S.val))) :
    (principalSubsetSectionTransport A r f M T).hom
      (((modulesSpecToSheaf.map ψ).hom.app (op (principalSubsetOpen A r f T.val)))
        ((modulesSpecToSheaf.obj N).obj.map (homOfLE hle).op
          (((modulesSpecToSheaf.map φ).hom.app (op (principalSubsetOpen A r f S.val)))
            x))) =
      ((alternatingCechModulePresheaf.obj
        ((SheafOfModules.overFunctor.{u} (moduleRings (Spec (.of A)).toRingedSpace)
          (principalSubsetUnion A r f) ⋙
            (Scheme.Modules.overEquiv (principalSubsetUnion A r f)).functor).obj M)).map
              (homOfLE hW).op).hom
        ((principalSubsetSectionTransport A r f M S).hom x) := by
  have hn := congrArg (fun z ↦ z
      (((modulesSpecToSheaf.map φ).hom.app (op (principalSubsetOpen A r f S.val))) x))
    ((modulesSpecToSheaf.map ψ).hom.naturality (homOfLE hle).op)
  have hc : ((modulesSpecToSheaf.map ψ).hom.app
      (op (principalSubsetOpen A r f S.val)))
      (((modulesSpecToSheaf.map φ).hom.app
        (op (principalSubsetOpen A r f S.val))) x) = x := by
    have hh := congrArg (fun g ↦ (g.hom.app (op (principalSubsetOpen A r f S.val))) x)
      (show modulesSpecToSheaf.map φ ≫ modulesSpecToSheaf.map ψ = 𝟙 _ by
        rw [← modulesSpecToSheaf.map_comp, hφψ, modulesSpecToSheaf.map_id])
    exact hh
  have hinner : ((modulesSpecToSheaf.map ψ).hom.app
      (op (principalSubsetOpen A r f T.val)))
      ((modulesSpecToSheaf.obj N).obj.map (homOfLE hle).op
        (((modulesSpecToSheaf.map φ).hom.app (op (principalSubsetOpen A r f S.val))) x)) =
        (modulesSpecToSheaf.obj M).obj.map (homOfLE hle).op x := by
    exact hn.trans (congrArg ((modulesSpecToSheaf.obj M).obj.map (homOfLE hle).op) hc)
  rw [hinner]
  exact transport_restriction A r f M S T hle hW x

private theorem supported_restriction
    (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A)
    (J : CochainComplex (Spec (.of A)).Modules ℤ) (n d : ℤ)
    (S₀ E T : {S : Finset (Fin r) // S.Nonempty}) (hE : E = S₀)
    (h₁ : n + 1 - (E.val.card : ℤ) = d)
    (h₂ : d = n + 1 - (S₀.val.card : ℤ))
    (hle : principalSubsetOpen A r f T.val ≤ principalSubsetOpen A r f E.val) :
    let V := principalSubsetUnion A r f
    let U : Fin r → V.toScheme.Opens := fun i ↦ V.ι ⁻¹ᵁ PrimeSpectrum.basicOpen (f i)
    let M := J.X (n + 1 - (S₀.val.card : ℤ))
    let P := alternatingCechModulePresheaf.obj
      ((SheafOfModules.overFunctor.{u} (moduleRings (Spec (.of A)).toRingedSpace) V ⋙
        (Scheme.Modules.overEquiv V).functor).obj M)
    ∀ (W : V.toScheme.Opens)
      (hsrc : W ≤ alternatingCechIntersection U (principalSubsetTuple r S₀))
      (htgt : W ≤ alternatingCechIntersection U (principalSubsetTuple r T))
      (x : (modulesSpecToSheaf.obj M).obj.obj (op (principalSubsetOpen A r f S₀.val))),
      (P.map (homOfLE hsrc).op).hom
        ((principalSubsetSectionTransport A r f M S₀).hom x) =
      (P.map (homOfLE htgt).op).hom
        ((principalSubsetSectionTransport A r f M T).hom
          (((modulesSpecToSheaf.map (eqToHom (congrArg J.X h₂))).hom.app
            (op (principalSubsetOpen A r f T.val)))
            ((modulesSpecToSheaf.obj (J.X d)).obj.map (homOfLE hle).op
              (((modulesSpecToSheaf.map (eqToHom (congrArg J.X h₁))).hom.app
                (op (principalSubsetOpen A r f E.val)))
                ((Pi.single S₀ x : principalSubsetCoordinates A r f J n) E))))) := by
  classical
  subst E
  intro V U M P W hsrc htgt x
  rw [Pi.single_eq_same]
  have hcan : alternatingCechIntersection U (principalSubsetTuple r T) ≤
      alternatingCechIntersection U (principalSubsetTuple r S₀) := by
    dsimp only [U]
    rw [principalSubsetIntersection, principalSubsetIntersection]
    exact Scheme.Hom.preimage_mono V.ι hle
  have hcomp : eqToHom (congrArg J.X h₁) ≫ eqToHom (congrArg J.X h₂) = 𝟙 M := by
    rw [eqToHom_trans]
    rfl
  have hh := transport_restriction_cast A r f M (J.X d)
    (eqToHom (congrArg J.X h₁)) (eqToHom (congrArg J.X h₂)) hcomp S₀ T hle hcan x
  refine Eq.trans ?_ (congrArg (fun y ↦ (P.map (homOfLE htgt).op).hom y) hh).symm
  change (P.map (homOfLE hsrc).op).hom _ =
    (P.map (homOfLE htgt).op).hom ((P.map (homOfLE hcan).op).hom _)
  rw [← Functor.map_comp_apply]
  congr 1

private theorem intersection_enumeration {X : Scheme.{u}} {r k l : ℕ}
    (U : Fin r → X.Opens) (S : Finset (Fin r)) (hk : S.card = k) (hl : S.card = l) :
    (⨅ i, U (S.orderEmbOfFin hk i)) = ⨅ i, U (S.orderEmbOfFin hl i) := by
  apply le_antisymm
  · apply le_iInf
    intro i
    obtain ⟨j, hj⟩ := (Finset.range_orderEmbOfFin S hk).ge
      (Finset.orderEmbOfFin_mem S hl i)
    exact hj ▸ iInf_le (fun j ↦ U (S.orderEmbOfFin hk j)) j
  · apply le_iInf
    intro i
    obtain ⟨j, hj⟩ := (Finset.range_orderEmbOfFin S hl).ge
      (Finset.orderEmbOfFin_mem S hk i)
    exact hj ▸ iInf_le (fun j ↦ U (S.orderEmbOfFin hl j)) j

private theorem single_eval_transport {X : Scheme.{u}} {R : Type u} [Ring R]
    {r p : ℕ} (U : Fin r → X.Opens) (P : X.Opensᵒᵖ ⥤ ModuleCat.{u} R)
    (t v : Fin (p + 1) ↪o Fin r) (h : v = t)
    (x : P.obj (op (alternatingCechIntersection U t))) :
    (Pi.single t x : ∀ t, P.obj (op (alternatingCechIntersection U t))) v =
      (P.map (eqToHom (congrArg (alternatingCechIntersection U) h)).op).hom x := by
  classical
  subst v
  rw [Pi.single_eq_same]
  change x = (P.map (𝟙 (op (alternatingCechIntersection U t)))).hom x
  rw [P.map_id]
  rfl

private theorem section_open_cast {X : Scheme.{u}} {R : Type u} [Ring R]
    (P : X.Opensᵒᵖ ⥤ ModuleCat.{u} R) {V W : X.Opens} (h : V = W)
    (x : P.obj (op W)) : HEq ((P.map (eqToHom h).op).hom x) x := by
  subst W
  apply heq_of_eq
  change (P.map (𝟙 (op V))).hom x = x
  rw [P.map_id]
  rfl

private theorem transport_cast
    (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A)
    (M N : (Spec (.of A)).Modules) (h : N = M)
    (S : {S : Finset (Fin r) // S.Nonempty})
    (x : (modulesSpecToSheaf.obj N).obj.obj (op (principalSubsetOpen A r f S.val))) :
    HEq ((principalSubsetSectionTransport A r f M S).hom
        ((modulesSpecToSheaf.map (eqToHom h)).hom.app
          (op (principalSubsetOpen A r f S.val)) x))
      ((principalSubsetSectionTransport A r f N S).hom x) := by
  subst N
  rfl

/-- The horizontal differential at one increasing target tuple.

Source: Stacks Project, Tag 01FG, ordered-complex differential, and Tags 08C0 and 08C1.
(blueprint: lem-sc-principal-open-cech-subset-horizontal-face-coordinate).

Proof: Expand the alternating differential at the increasing enumeration of S.
Biject deleted positions with elements j of S. Deleting position j enumerates
S.erase j, and the position equals the number of elements below j. A source
singleton contributes only if that erased subset is S₀, since increasing
embeddings with equal ranges agree. Naturality of overFunctorEquiv, restriction
and the coefficient presheaf identifies the face map with restriction on the
principal opens. The degree equality he and the cardinality assumption identify
the coefficients; functoriality and proof irrelevance identify all transports.
The integer sign action agrees with the action of (-1 : A) to the same power.
Summing the terms gives the displayed equality. Since S has cardinality at least
two, each deletion is nonempty. For r=0 or r=1 no such target subset exists. -/
theorem principalSubsetHorizontalFaceCoordinate
    (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A)
    (J : CochainComplex (Spec (.of A)).Modules ℤ) :
    let V := principalSubsetUnion A r f
    let U : Fin r → V.toScheme.Opens := fun i ↦ V.ι ⁻¹ᵁ PrimeSpectrum.basicOpen (f i)
    let D := principalSubsetOpen A r f
    ∀ (hle : ∀ (S : Finset (Fin r)) (j : Fin r), D S ≤ D (S.erase j))
      (he : ∀ (S : Finset (Fin r)) (j : Fin r), j ∈ S → ∀ n : ℤ,
        n + 1 - ((S.erase j).card : ℤ) = n + 1 + 1 - (S.card : ℤ))
      (n : ℤ) (S₀ : {S : Finset (Fin r) // S.Nonempty})
      (x : (modulesSpecToSheaf.obj (J.X (n + 1 - (S₀.val.card : ℤ)))).obj.obj
        (op (D S₀.val))),
      let p := S₀.val.card - 1
      let q := n + 1 - (S₀.val.card : ℤ)
      let P := alternatingCechModulePresheaf.obj ((principalSubsetRestriction A r f J).X q)
      ∀ (S : {S : Finset (Fin r) // S.Nonempty}) (hcard : S.val.card = p + 2),
      HEq (((alternatingCechDifferential U P p).hom
          (Pi.single (principalSubsetTuple r S₀)
            ((principalSubsetSectionTransport A r f (J.X q) S₀).hom x)))
          (S.val.orderEmbOfFin hcard))
        ((principalSubsetSectionTransport A r f
          (J.X (n + 1 + 1 - (S.val.card : ℤ))) S).hom (
          ∑ j : S.val, if h : (S.val.erase j.val).Nonempty then
            (-1 : A) ^ ((S.val.filter (fun i ↦ i < j.val)).card) •
              (modulesSpecToSheaf.obj (J.X (n + 1 + 1 - (S.val.card : ℤ)))).obj.map
                (homOfLE (hle S.val j.val)).op
                ((modulesSpecToSheaf.map
                  (eqToHom (congrArg J.X (he S.val j.val j.property n)))).hom.app
                    (op (D (S.val.erase j.val)))
                    ((Pi.single S₀ x : principalSubsetCoordinates A r f J n)
                      ⟨S.val.erase j.val, h⟩))
          else 0)) := by
  classical
  intro V U D hle he n S₀ x p q P S hcard
  have hq : n + 1 - (S₀.val.card : ℤ) = n + 1 + 1 - (S.val.card : ℤ) := by
    have := S₀.property.card_pos
    dsimp only [p] at hcard
    omega
  apply HEq.trans ?_ (transport_cast A r f (J.X q)
    (J.X (n + 1 + 1 - (S.val.card : ℤ))) (congrArg J.X hq.symm) S _)
  let z : P.obj (op (alternatingCechIntersection U (principalSubsetTuple r S))) :=
    (principalSubsetSectionTransport A r f (J.X q) S).hom
      ((modulesSpecToSheaf.map (eqToHom (congrArg J.X hq.symm))).hom.app
        (op (D S.val)) (
          ∑ j : S.val, if h : (S.val.erase j.val).Nonempty then
            (-1 : A) ^ ((S.val.filter (fun i ↦ i < j.val)).card) •
              (modulesSpecToSheaf.obj (J.X (n + 1 + 1 - (S.val.card : ℤ)))).obj.map
                (homOfLE (hle S.val j.val)).op
                ((modulesSpecToSheaf.map
                  (eqToHom (congrArg J.X (he S.val j.val j.property n)))).hom.app
                    (op (D (S.val.erase j.val)))
                    ((Pi.single S₀ x : principalSubsetCoordinates A r f J n)
                      ⟨S.val.erase j.val, h⟩))
          else 0))
  change HEq _ z
  have hW : alternatingCechIntersection U (S.val.orderEmbOfFin hcard) =
      alternatingCechIntersection U (principalSubsetTuple r S) :=
    intersection_enumeration U S.val hcard _
  refine HEq.trans ?_ (section_open_cast P hW z)
  apply heq_of_eq
  rw [alternatingRow_d_apply]
  let b := (P.map (eqToHom hW).op).hom.toAddMonoidHom.comp
    ((AddCommGrpCat.homAddEquiv
      (principalSubsetSectionTransport A r f (J.X q) S).hom).comp
        ((modulesSpecToSheaf.map (eqToHom (congrArg J.X hq.symm))).hom.app
          (op (D S.val))).hom.toAddMonoidHom)
  change (∑ k, _) = b (∑ j, _)
  rw [map_sum]
  apply Fintype.sum_equiv (S.val.orderIsoOfFin hcard).toEquiv
  intro k
  have hk : (S.val.filter
      (fun i ↦ i < (S.val.orderIsoOfFin hcard k).val)).card = k.val :=
    countBefore r (p + 1) ⟨S.val, hcard⟩ k
  erw [hk]
  have hn : (S.val.erase (S.val.orderIsoOfFin hcard k).val).Nonempty := by
    apply Finset.card_pos.mp
    rw [Finset.card_erase_of_mem (S.val.orderIsoOfFin hcard k).property, hcard]
    omega
  erw [dite_eq_left hn]
  erw [show (-1 : A) ^ k.val = (((-1 : ℤ) ^ k.val : ℤ) : A) by simp,
    Int.cast_smul_eq_zsmul A, b.map_zsmul]
  congr 1
  let E : {S : Finset (Fin r) // S.Nonempty} :=
    ⟨S.val.erase (S.val.orderIsoOfFin hcard k).val, hn⟩
  let v : Fin (p + 1) ↪o Fin r :=
    (Fin.succAboveOrderEmb k).trans (S.val.orderEmbOfFin hcard)
  have hv : Finset.univ.image v = E.val := by
    change Finset.univ.image ((S.val.orderEmbOfFin hcard) ∘ k.succAbove) = _
    rw [eraseEnumeration r p ⟨S.val, hcard⟩ k]
    exact Finset.image_orderEmbOfFin_univ _ _
  by_cases hE : E = S₀
  · have ht : v = principalSubsetTuple r S₀ := by
      apply Finset.orderEmbOfFin_unique'
      intro i
      have hi : v i ∈ E.val := hv ▸ Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
      exact hE ▸ hi
    change (P.map (homOfLE (alternatingCechIntersection_face_le U p
      (S.val.orderEmbOfFin hcard) k)).op).hom
      ((Pi.single (principalSubsetTuple r S₀)
        ((principalSubsetSectionTransport A r f (J.X q) S₀).hom x) :
          alternatingCechTerms U P p) v) = _
    rw [single_eval_transport U P (principalSubsetTuple r S₀) v ht]
    have hsrc : alternatingCechIntersection U (S.val.orderEmbOfFin hcard) ≤
        alternatingCechIntersection U (principalSubsetTuple r S₀) := by
      rw [← ht]
      exact alternatingCechIntersection_face_le U p (S.val.orderEmbOfFin hcard) k
    have htgt : alternatingCechIntersection U (S.val.orderEmbOfFin hcard) ≤
        alternatingCechIntersection U (principalSubsetTuple r S) := hW.le
    have hh := supported_restriction A r f J n
      (n + 1 + 1 - (S.val.card : ℤ)) S₀ E S hE
      (he S.val (S.val.orderIsoOfFin hcard k).val
        (S.val.orderIsoOfFin hcard k).property n) hq.symm
      (hle S.val (S.val.orderIsoOfFin hcard k).val)
      (alternatingCechIntersection U (S.val.orderEmbOfFin hcard)) hsrc htgt x
    change _ = (P.map (eqToHom hW).op).hom
      ((principalSubsetSectionTransport A r f (J.X q) S).hom
        (((modulesSpecToSheaf.map (eqToHom (congrArg J.X hq.symm))).hom.app
          (op (D S.val)))
          ((modulesSpecToSheaf.obj (J.X (n + 1 + 1 - (S.val.card : ℤ)))).obj.map
            (homOfLE (hle S.val (S.val.orderIsoOfFin hcard k).val)).op
            (((modulesSpecToSheaf.map
              (eqToHom (congrArg J.X (he S.val (S.val.orderIsoOfFin hcard k).val
                (S.val.orderIsoOfFin hcard k).property n)))).hom.app
                  (op (D E.val))) ((Pi.single S₀ x :
                    principalSubsetCoordinates A r f J n) E)))))
    refine Eq.trans ?_ hh
    rw [← Functor.map_comp_apply]
    congr 1
  · have ht : v ≠ principalSubsetTuple r S₀ := by
      intro hh
      apply hE
      apply Subtype.ext
      rw [← hv, hh]
      exact Finset.image_orderEmbOfFin_univ _ _
    change (P.map (homOfLE (alternatingCechIntersection_face_le U p
      (S.val.orderEmbOfFin hcard) k)).op).hom
      ((Pi.single (principalSubsetTuple r S₀)
        ((principalSubsetSectionTransport A r f (J.X q) S₀).hom x) :
          alternatingCechTerms U P p) v) = _
    rw [Pi.single_eq_of_ne ht, map_zero]
    have hz : (Pi.single S₀ x : principalSubsetCoordinates A r f J n) E = 0 := by
      rw [Pi.single_eq_of_ne hE]
    dsimp only [E] at hz
    erw [hz]
    simp only [map_zero]

end AlgebraicGeometry
