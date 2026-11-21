import Langlands.AbelianScheme.PolarizedFiniteLevel.FrameEmbeddingHilbertPolynomial
import Langlands.AlgebraicGeometry.ProjectiveSpace.TwistOnePresentation

/-! # A finite-type ambient family for frame-normalized cubic embeddings -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

open Langlands.AlgebraicGeometry RelativeProjectiveSpace

/-- An ambient projective family with integral projective points, of finite type over
`Spec ℤ`, through which the projective presentation of every frame embedding classifies
uniquely. The family itself is not asserted to consist of polarized data. -/
structure CubicFrameClassifyingFamily (g d n m : ℕ) where
  base : Scheme.{u}
  ideal : (RelativeProjectiveSpace base m).IdealSheafData
  points : (Fin (2 * g) → ZMod n) → (base ⟶ ProjectiveSpace (ULift.{u} ℤ) m)
  noetherian : IsNoetherian base
  locallyOfFiniteType : LocallyOfFiniteType (specULiftZIsTerminal.from base)
  flat : Flat (ideal.subschemeι ≫ toBase base m)
  locallyOfFinitePresentation : LocallyOfFinitePresentation (ideal.subschemeι ≫ toBase base m)
  classifies : ∀ {P : Prerequisites.{u}} {T : Scheme.{u}}
    (b : Datum P T g d n) (ρ : Fin (m + 2) → Fin (2 * g) → ZMod n)
    (ψ : b.abelian.X.left ⟶ RelativeProjectiveSpace T m), b.IsFrameEmbedding ρ ψ →
    ∃! t : T ⟶ base, ideal.comap (map m t) = ψ.ker ∧
      ∀ r, t ≫ points r = b.torsionPoint r ≫ ψ ≫ toIntegral T m

private theorem isProper_iterateToBase (m : ℕ) (Y : Scheme.{u}) :
    ∀ k, IsProper (iterateToBase m Y k)
  | 0 => inferInstanceAs (IsProper (𝟙 Y))
  | k + 1 => by
    have := isProper_iterateToBase m Y k
    exact inferInstanceAs (IsProper (toBase (iterate m Y k) m ≫ iterateToBase m Y k))

private theorem comap_iso_injective {X Y : Scheme.{u}} (e : X ≅ Y) :
    Function.Injective (fun I : Y.IdealSheafData => I.comap e.hom) := by
  intro I J h
  simpa only [← Scheme.IdealSheafData.comap_comp, Iso.inv_hom_id,
    Scheme.IdealSheafData.comap_id] using
    congrArg (fun K : X.IdealSheafData => K.comap e.inv) h

private theorem frameIdeal_comap {X T : Scheme.{u}} {m : ℕ}
    (ψ : X ⟶ RelativeProjectiveSpace T m) [IsClosedImmersion ψ]
    (s : T ⟶ Spec (CommRingCat.of (ULift.{u} ℤ))) :
    (ψ ≫ (isoPullbackSpec m s).hom).ker.comap (isoPullbackSpec m s).hom = ψ.ker := by
  let e := isoPullbackSpec m s
  have h : IsPullback ψ (𝟙 X) e.hom (ψ ≫ e.hom) :=
    IsPullback.of_vert_isIso ⟨(Category.id_comp _).symm⟩
  rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion]
  simpa only [Scheme.Hom.ker_comp_of_isIso] using congrArg Scheme.Hom.ker h.isoPullback_hom_fst

/-- Restrict the published Hilbert family for `𝒪(1)` to the cubic Hilbert polynomial;
adjoin the finitely many integral projective points by iteration. -/
theorem nonempty_cubicFrameClassifyingFamily (g d n m : ℕ) [NeZero n] :
    Nonempty (CubicFrameClassifyingFamily.{u} g d n m) := by
  let f := projectiveSpaceToSpec (ULift.{u} ℤ) m
  obtain ⟨H, πH, W, -, -, huniv, U, -, -, hpiece⟩ :=
    HilbertSchemeUniversalFamily.hilbertSchemeUniversalFamily.{u} (ULift.{u} ℤ) f
      (twistOne (ULift.{u} ℤ) m) inferInstance inferInstance (twistOne_isInvertible _ _)
      (twistOne_closedImmersionBySections _ _)
  let θ := cubicHilbertPolynomial g d
  let O := U θ
  let R := Fin (2 * g) → ZMod n
  let N := Fintype.card R
  let e := Fintype.equivFin R
  let S := iterate m O.toScheme N
  let q := iterateToBase m O.toScheme N
  let W' := W.comap (isoPullbackSpec m πH).hom
  let IS := W'.comap (map m (q ≫ O.ι))
  have : IsNoetherianRing (ULift.{u} ℤ) :=
    isNoetherianRing_of_ringEquiv ℤ ULift.ringEquiv.symm
  have : IsProper (O.ι ≫ πH) := (hpiece θ).1.isProper
  have : IsProper q := isProper_iterateToBase m _ N
  have hproper : IsProper (specULiftZIsTerminal.from S) := by
    rw [specULiftZIsTerminal.hom_ext (specULiftZIsTerminal.from S) (q ≫ O.ι ≫ πH)]
    infer_instance
  have : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian
    (specULiftZIsTerminal.from S)
  have : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace
    (specULiftZIsTerminal.from S)
  have hnoeth : IsNoetherian S := ⟨⟩
  have htrans {T : Scheme.{u}} (v : T ⟶ H) (s : T ⟶ Spec (CommRingCat.of (ULift.{u} ℤ)))
      (hv : v ≫ πH = s) :
      W'.comap (map m v) =
        (W.comap (pullback.map f s f πH (𝟙 _) v (𝟙 _) (by simp)
          (by simp [hv]))).comap (isoPullbackSpec m s).hom := by
    simp only [W', ← Scheme.IdealSheafData.comap_comp]
    rw [map_isoPullbackSpec_hom m v πH s hv]
  refine ⟨{
    base := S
    ideal := IS
    points := fun r => iterateCoord m O.toScheme N (e r)
    noetherian := hnoeth
    locallyOfFiniteType := inferInstance
    flat := ?_
    locallyOfFinitePresentation := ?_
    classifies := ?_ }⟩
  · dsimp only [IS]
    rw [htrans (q ≫ O.ι) _ rfl, (comap_isoPullbackSpec_iff m _ _).1]
    exact ((huniv _ ((q ≫ O.ι) ≫ πH)).1 (q ≫ O.ι) rfl).1
  · dsimp only [IS]
    rw [htrans (q ≫ O.ι) _ rfl, (comap_isoPullbackSpec_iff m _ _).2]
    exact ((huniv _ ((q ≫ O.ι) ≫ πH)).1 (q ≫ O.ι) rfl).2
  · intro P T b ρ ψ hψ
    let s := specULiftZIsTerminal.from T
    let J := (ψ ≫ (isoPullbackSpec m s).hom).ker
    have := hψ.isClosedImmersion
    have hJ : J.comap (isoPullbackSpec m s).hom = ψ.ker := frameIdeal_comap ψ s
    have hflat : Flat (J.subschemeι ≫ pullback.snd _ _) := by
      rw [← (comap_isoPullbackSpec_iff m s J).1, hJ]
      exact hψ.flat
    have hlfp : LocallyOfFinitePresentation (J.subschemeι ≫ pullback.snd _ _) := by
      rw [← (comap_isoPullbackSpec_iff m s J).2, hJ]
      exact hψ.locallyOfFinitePresentation
    obtain ⟨v, ⟨hv, hvW⟩, hvuniq⟩ := (huniv T s).2 J hflat hlfp
    have hvO : Set.range v.base ⊆ (O : Set H) := by
      rintro y ⟨x, rfl⟩
      let tx := T.fromSpecResidueField x
      let sx := tx ≫ s
      let vx := tx ≫ v
      have hvx : vx ≫ πH = sx := by simp [vx, sx, Category.assoc, hv]
      let Jx := W.comap (pullback.map f sx f πH (𝟙 _) vx (𝟙 _) (by simp) (by simp [hvx]))
      let ψx := b.pullbackEmbedding tx ψ
      have hψx := hψ.pullback (f := tx)
      have hbar : b.Realizes ψ ψ.ker (fun r => b.torsionPoint r ≫ ψ ≫ toIntegral T m) :=
        ⟨rfl, fun _ => rfl⟩
      have hJx : Jx.comap (isoPullbackSpec m sx).hom = ψx.ker := by
        have hpb := (hbar.pullback (f := tx) hψ).1
        rw [← htrans vx sx hvx]
        change W'.comap (map m (tx ≫ v)) = ψx.ker
        rw [map_comp, Scheme.IdealSheafData.comap_comp, htrans v s hv, hvW, hJ]
        exact hpb.symm
      have := hψx.isClosedImmersion
      have hJx' : (ψx ≫ (isoPullbackSpec m sx).hom).ker = Jx :=
        comap_iso_injective (isoPullbackSpec m sx) ((frameIdeal_comap ψx sx).trans hJx.symm)
      have hmem : Set.range vx.base ⊆ (O : Set H) := by
        apply ((hpiece θ).2 _ sx vx hvx Jx rfl).mpr
        intro K _ _ sk
        exact ⟨1, fun k hk => hψx.geomFibreH0Finrank_eq_cubicHilbertPolynomial sx Jx hJx'
          K sk k hk⟩
      apply hmem
      refine ⟨IsLocalRing.closedPoint (T.residueField x), ?_⟩
      change v (tx _) = v x
      rw [Scheme.fromSpecResidueField_apply]
    let u := IsOpenImmersion.lift O.ι v (by simpa only [Scheme.Opens.range_ι] using hvO)
    have hu : u ≫ O.ι = v := IsOpenImmersion.lift_fac _ _ _
    let σ := fun r : R => b.torsionPoint r ≫ ψ ≫ toIntegral T m
    refine ⟨iterateLift m O.toScheme N u (fun i => σ (e.symm i)), ⟨?_, fun r => ?_⟩, ?_⟩
    · change IS.comap _ = _
      rw [← Scheme.IdealSheafData.comap_comp, ← map_comp, ← Category.assoc,
        iterateLift_toBase, hu, htrans v s hv, hvW, hJ]
    · rw [iterateLift_coord, Equiv.symm_apply_apply]
    · intro t' ⟨ht'I, ht'σ⟩
      have ht'q : t' ≫ q ≫ O.ι = v := by
        apply hvuniq
        have ht's : (t' ≫ q ≫ O.ι) ≫ πH = s := specULiftZIsTerminal.hom_ext _ _
        refine ⟨ht's, comap_iso_injective (isoPullbackSpec m s) ?_⟩
        dsimp only
        rw [← htrans _ s ht's, hJ, map_comp, Scheme.IdealSheafData.comap_comp]
        exact ht'I
      apply iterate_hom_ext O.toScheme N
      · rw [iterateLift_toBase, ← cancel_mono O.ι, Category.assoc, hu]
        exact ht'q
      · intro i
        rw [iterateLift_coord]
        simpa only [Equiv.apply_symm_apply] using ht'σ (e.symm i)

end Langlands.AbelianScheme.PolarizedFiniteLevel
