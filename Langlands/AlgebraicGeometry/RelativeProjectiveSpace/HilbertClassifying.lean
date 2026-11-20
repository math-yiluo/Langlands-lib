import Langlands.AlgebraicGeometry.HilbertSchemeUniversalFamilyProof
import Langlands.AlgebraicGeometry.ProjectiveSpace.FlatStructure
import Langlands.AlgebraicGeometry.Picard.ProperAmpleClosedImmersionBySectionsStatement
import Langlands.AlgebraicGeometry.RelativeProjectiveSpace.Geometry

/-! # A classifying scheme for flat projective families with finitely many points -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

namespace RelativeProjectiveSpace

variable (m : ℕ)

/-- Relative projective space over `T` is the fibre product of the integral projective
space with `T` over `Spec ℤ`, in the presentation used by the Hilbert scheme. -/
def isoPullbackSpec {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of (ULift.{u} ℤ))) :
    RelativeProjectiveSpace T m ≅ pullback (projectiveSpaceToSpec (ULift.{u} ℤ) m) s where
  hom := pullback.lift (toIntegral T m) (toBase T m) (specULiftZIsTerminal.hom_ext _ _)
  inv := lift m (pullback.snd _ _) (pullback.fst _ _)
  hom_inv_id := by
    apply hom_ext
    · rw [Category.assoc, lift_toBase, pullback.lift_snd, Category.id_comp]
    · rw [Category.assoc, lift_toIntegral, pullback.lift_fst, Category.id_comp]
  inv_hom_id := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, lift_toIntegral, Category.id_comp]
    · rw [Category.assoc, pullback.lift_snd, lift_toBase, Category.id_comp]

/-- The comparison is compatible with change of base. -/
lemma map_isoPullbackSpec_hom {T T' : Scheme.{u}} (t : T' ⟶ T)
    (s : T ⟶ Spec (CommRingCat.of (ULift.{u} ℤ)))
    (s' : T' ⟶ Spec (CommRingCat.of (ULift.{u} ℤ))) (h : t ≫ s = s') :
    map m t ≫ (isoPullbackSpec m s).hom =
      (isoPullbackSpec m s').hom ≫
        pullback.map _ _ _ _ (𝟙 _) t (𝟙 _) (by simp) (by simp [h]) := by
  apply pullback.hom_ext
  · simp only [isoPullbackSpec, Category.assoc, pullback.lift_fst,
      map_toIntegral, Category.comp_id]
  · simp only [isoPullbackSpec, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc,
      map_toBase]

/-- The closed subscheme of relative projective space corresponding to a closed subscheme of
the fibre product has the same structure morphism up to an isomorphism. -/
lemma comap_isoPullbackSpec_subschemeι_toBase {T : Scheme.{u}}
    (s : T ⟶ Spec (CommRingCat.of (ULift.{u} ℤ)))
    (J : (pullback (projectiveSpaceToSpec (ULift.{u} ℤ) m) s).IdealSheafData) :
    (J.comap (isoPullbackSpec m s).hom).subschemeι ≫ toBase T m =
      ((J.comapIso (isoPullbackSpec m s).hom).hom ≫
        pullback.snd (isoPullbackSpec m s).hom J.subschemeι) ≫
          (J.subschemeι ≫ pullback.snd _ _) := by
  rw [← Scheme.IdealSheafData.comapIso_hom_fst]
  simp only [Category.assoc]
  have h1 : toBase T m = (isoPullbackSpec m s).hom ≫ pullback.snd _ _ := by
    simp [isoPullbackSpec]
  rw [h1, pullback.condition_assoc]

/-- Flatness and local finite presentation transfer between the two presentations. -/
lemma comap_isoPullbackSpec_iff {T : Scheme.{u}}
    (s : T ⟶ Spec (CommRingCat.of (ULift.{u} ℤ)))
    (J : (pullback (projectiveSpaceToSpec (ULift.{u} ℤ) m) s).IdealSheafData) :
    (Flat ((J.comap (isoPullbackSpec m s).hom).subschemeι ≫ toBase T m) ↔
      Flat (J.subschemeι ≫ pullback.snd _ _)) ∧
    (LocallyOfFinitePresentation ((J.comap (isoPullbackSpec m s).hom).subschemeι ≫
        toBase T m) ↔
      LocallyOfFinitePresentation (J.subschemeι ≫ pullback.snd _ _)) := by
  rw [comap_isoPullbackSpec_subschemeι_toBase]
  set φ := (J.comapIso (isoPullbackSpec m s).hom).hom ≫
    pullback.snd (isoPullbackSpec m s).hom J.subschemeι
  have hφ : J.subschemeι ≫ pullback.snd _ _ =
      inv φ ≫ (φ ≫ (J.subschemeι ≫ pullback.snd _ _)) := by
    rw [IsIso.inv_hom_id_assoc]
  refine ⟨⟨fun h => ?_, fun h => inferInstance⟩, ⟨fun h => ?_, fun h => inferInstance⟩⟩
  · rw [hφ]; infer_instance
  · rw [hφ]; infer_instance

/-- `k` successive relative projective `m`-spaces over `H`. -/
def iterate (H : Scheme.{u}) : ℕ → Scheme.{u}
  | 0 => H
  | k + 1 => RelativeProjectiveSpace (iterate H k) m

/-- The structure morphism of the iterated relative projective space. -/
def iterateToBase (H : Scheme.{u}) : (k : ℕ) → iterate m H k ⟶ H
  | 0 => 𝟙 H
  | k + 1 => toBase (iterate m H k) m ≫ iterateToBase H k

/-- The `k` integral coordinates of the iterated relative projective space. -/
def iterateCoord (H : Scheme.{u}) :
    (k : ℕ) → Fin k → (iterate m H k ⟶ ProjectiveSpace (ULift.{u} ℤ) m)
  | 0, i => i.elim0
  | k + 1, i => Fin.lastCases (toIntegral (iterate m H k) m)
      (fun i => toBase (iterate m H k) m ≫ iterateCoord H k i) i

/-- A morphism to the iterated relative projective space from a morphism to `H` and `k`
integral projective points. -/
def iterateLift (H : Scheme.{u}) {T : Scheme.{u}} :
    (k : ℕ) → (T ⟶ H) → (Fin k → (T ⟶ ProjectiveSpace (ULift.{u} ℤ) m)) → (T ⟶ iterate m H k)
  | 0, h, _ => h
  | k + 1, h, σ => lift m (iterateLift H k h (fun i => σ i.castSucc)) (σ (Fin.last k))

variable {m}

@[simp]
lemma iterateLift_toBase (H : Scheme.{u}) {T : Scheme.{u}} :
    ∀ (k : ℕ) (h : T ⟶ H) (σ : Fin k → (T ⟶ ProjectiveSpace (ULift.{u} ℤ) m)),
      iterateLift m H k h σ ≫ iterateToBase m H k = h
  | 0, h, σ => Category.comp_id h
  | k + 1, h, σ => by
    simp only [iterateLift, iterateToBase]
    rw [lift_toBase_assoc]
    exact iterateLift_toBase H k h _

@[simp]
lemma iterateLift_coord (H : Scheme.{u}) {T : Scheme.{u}} :
    ∀ (k : ℕ) (h : T ⟶ H) (σ : Fin k → (T ⟶ ProjectiveSpace (ULift.{u} ℤ) m)) (i : Fin k),
      iterateLift m H k h σ ≫ iterateCoord m H k i = σ i
  | 0, h, σ, i => i.elim0
  | k + 1, h, σ, i => by
    induction i using Fin.lastCases with
    | last =>
      simp only [iterateLift, iterateCoord, Fin.lastCases_last]
      exact lift_toIntegral _ _ _
    | cast i =>
      simp only [iterateLift, iterateCoord, Fin.lastCases_castSucc]
      rw [lift_toBase_assoc]
      exact iterateLift_coord H k h _ i

lemma iterate_hom_ext (H : Scheme.{u}) {T : Scheme.{u}} :
    ∀ (k : ℕ) {f f' : T ⟶ iterate m H k},
      f ≫ iterateToBase m H k = f' ≫ iterateToBase m H k →
      (∀ i, f ≫ iterateCoord m H k i = f' ≫ iterateCoord m H k i) → f = f'
  | 0, f, f', h, _ => by
    have h' := h
    simp only [iterateToBase] at h'
    erw [Category.comp_id, Category.comp_id] at h'
    exact h'
  | k + 1, f, f', h, hc => by
    apply hom_ext
    · apply iterate_hom_ext H k
      · simpa only [iterateToBase, Category.assoc] using h
      · intro i
        have := hc i.castSucc
        simpa only [iterateCoord, Fin.lastCases_castSucc, Category.assoc] using this
    · have := hc (Fin.last k)
      simpa only [iterateCoord, Fin.lastCases_last] using this

instance isLocallyNoetherian_relativeProjectiveSpace (S : Scheme.{u}) [IsLocallyNoetherian S] :
    IsLocallyNoetherian (RelativeProjectiveSpace S m) :=
  LocallyOfFiniteType.isLocallyNoetherian (toBase S m)

instance isLocallyNoetherian_iterate (H : Scheme.{u}) [IsLocallyNoetherian H] :
    ∀ k, IsLocallyNoetherian (iterate m H k)
  | 0 => ‹_›
  | k + 1 => by
    have := isLocallyNoetherian_iterate H k
    exact isLocallyNoetherian_relativeProjectiveSpace (iterate m H k)

end RelativeProjectiveSpace

open RelativeProjectiveSpace

/-- There is a locally noetherian scheme `S` with a flat, locally finitely presented closed
subscheme of relative projective `m`-space over it and integral projective points `σS r`,
`r ∈ R`, classifying all such data: for every scheme `T`, flat, locally finitely presented
closed subschemes of `ℙ^m_T` with points indexed by `R` correspond to morphisms `T ⟶ S`.
It is the Hilbert scheme of `ℙ^m_ℤ` (published `hilbertSchemeUniversalFamily`) followed by
`|R|` successive relative projective spaces. -/
theorem exists_relativeProjectiveFamily_classifying (m : ℕ) (R : Type*) [Fintype R] :
    ∃ (S : Scheme.{u}) (IS : (RelativeProjectiveSpace S m).IdealSheafData)
      (σS : R → (S ⟶ ProjectiveSpace (ULift.{u} ℤ) m)),
      IsLocallyNoetherian S ∧
      Flat (IS.subschemeι ≫ RelativeProjectiveSpace.toBase S m) ∧
      LocallyOfFinitePresentation (IS.subschemeι ≫ RelativeProjectiveSpace.toBase S m) ∧
      ∀ (T : Scheme.{u}) (I : (RelativeProjectiveSpace T m).IdealSheafData)
        (σ : R → (T ⟶ ProjectiveSpace (ULift.{u} ℤ) m)),
        Flat (I.subschemeι ≫ RelativeProjectiveSpace.toBase T m) →
        LocallyOfFinitePresentation (I.subschemeι ≫ RelativeProjectiveSpace.toBase T m) →
        ∃! t : T ⟶ S, IS.comap (RelativeProjectiveSpace.map m t) = I ∧
          ∀ r, t ≫ σS r = σ r := by
  have : IsNoetherianRing (ULift.{u} ℤ) :=
    isNoetherianRing_of_ringEquiv ℤ ULift.ringEquiv.symm
  obtain ⟨M, hM₁, hM₂⟩ :=
    (Picard.exists_closedImmersionBySections_iff_isHProjective
      (projectiveSpaceToSpec (ULift.{u} ℤ) m)).mpr
      ⟨m, 𝟙 _, inferInstance, Category.id_comp _⟩
  obtain ⟨H, πH, W, hlfp, -, huniv, -⟩ :=
    HilbertSchemeUniversalFamily.hilbertSchemeUniversalFamily.{u} (ULift.{u} ℤ)
      (projectiveSpaceToSpec (ULift.{u} ℤ) m) M inferInstance inferInstance hM₁ hM₂
  have : LocallyOfFiniteType πH := inferInstance
  have hH : IsLocallyNoetherian H := LocallyOfFiniteType.isLocallyNoetherian πH
  let e := Fintype.equivFin R
  let N := Fintype.card R
  let q := iterateToBase m H N
  let W' := W.comap (isoPullbackSpec m πH).hom
  -- the transport of the Hilbert family along a morphism to `H`
  have htrans : ∀ {T : Scheme.{u}} (t : T ⟶ H) (s : T ⟶ Spec (CommRingCat.of (ULift.{u} ℤ)))
      (hs : t ≫ πH = s),
      W'.comap (map m t) =
        (W.comap (pullback.map (projectiveSpaceToSpec (ULift.{u} ℤ) m) s
          (projectiveSpaceToSpec (ULift.{u} ℤ) m) πH (𝟙 _) t (𝟙 _) (by simp)
          (by simp [hs]))).comap (isoPullbackSpec m s).hom := by
    intro T t s hs
    simp only [W', ← Scheme.IdealSheafData.comap_comp]
    rw [map_isoPullbackSpec_hom m t πH s hs]
  refine ⟨iterate m H N, W'.comap (map m q), fun r => iterateCoord m H N (e r), inferInstance,
    ?_, ?_, ?_⟩
  · rw [htrans q _ rfl, (comap_isoPullbackSpec_iff m _ _).1]
    exact ((huniv _ (q ≫ πH)).1 q rfl).1
  · rw [htrans q _ rfl, (comap_isoPullbackSpec_iff m _ _).2]
    exact ((huniv _ (q ≫ πH)).1 q rfl).2
  · intro T I σ hfl hlp
    let s : T ⟶ Spec (CommRingCat.of (ULift.{u} ℤ)) := specULiftZIsTerminal.from T
    let J := I.comap (isoPullbackSpec m s).inv
    have hJ : J.comap (isoPullbackSpec m s).hom = I := by
      simp only [J, ← Scheme.IdealSheafData.comap_comp, Iso.hom_inv_id,
        Scheme.IdealSheafData.comap_id]
    have hJfl : Flat (J.subschemeι ≫ pullback.snd _ _) := by
      rw [← (comap_isoPullbackSpec_iff m _ _).1, hJ]
      exact hfl
    have hJlp : LocallyOfFinitePresentation (J.subschemeι ≫ pullback.snd _ _) := by
      rw [← (comap_isoPullbackSpec_iff m _ _).2, hJ]
      exact hlp
    obtain ⟨g, ⟨hg, hgW⟩, hguniq⟩ := (huniv T s).2 J hJfl hJlp
    refine ⟨iterateLift m H N g (fun i => σ (e.symm i)), ⟨?_, fun r => ?_⟩, ?_⟩
    · rw [← Scheme.IdealSheafData.comap_comp, ← map_comp, iterateLift_toBase,
        htrans g s hg, hgW, hJ]
    · rw [iterateLift_coord, Equiv.symm_apply_apply]
    · intro t' ⟨ht'I, ht'σ⟩
      have hq : t' ≫ q = g := by
        apply hguniq
        refine ⟨specULiftZIsTerminal.hom_ext _ _, ?_⟩
        have h1 : (W.comap (pullback.map (projectiveSpaceToSpec (ULift.{u} ℤ) m) s
            (projectiveSpaceToSpec (ULift.{u} ℤ) m) πH (𝟙 _) (t' ≫ q) (𝟙 _) (by simp)
            (by simp [specULiftZIsTerminal.hom_ext ((t' ≫ q) ≫ πH) s]))).comap
              (isoPullbackSpec m s).hom = I := by
          rw [← htrans (t' ≫ q) s (specULiftZIsTerminal.hom_ext _ _), map_comp,
            Scheme.IdealSheafData.comap_comp]
          exact ht'I
        rw [← hJ] at h1
        have h2 := congrArg (fun K => K.comap (isoPullbackSpec m s).inv) h1
        simpa only [← Scheme.IdealSheafData.comap_comp, Iso.inv_hom_id_assoc,
          Iso.inv_hom_id, Scheme.IdealSheafData.comap_id] using h2
      apply iterate_hom_ext H N
      · rw [iterateLift_toBase]
        exact hq
      · intro i
        rw [iterateLift_coord]
        have := ht'σ (e.symm i)
        simpa only [Equiv.apply_symm_apply] using this

end Langlands.AlgebraicGeometry
