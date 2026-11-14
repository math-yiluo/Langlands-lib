import Langlands.AlgebraicGeometry.Picard.PicardHilbertPiecesRepresentabilityReductionRelation

/-! # Proof of the reduction of the representability of the Picard pieces -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory Opposite

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard.PicardHilbertPiecesReduction

open ProperFlatIntegralSheafClassTwist Langlands.AlgebraicGeometry.AlgebraicSpace

section Image

variable {S X : Scheme.{u}} (f : X ⟶ S) {Z : Over S}
  (ζ0 : uliftYoneda.{u + 1}.obj Z ⟶ RelativePicard.classSheafPresheaf f)

/-- The fppf image sheaf of a morphism to the Picard class sheaf: the sheafification of its
image subpresheaf. -/
abbrev imageSheaf : FppfSheaf S :=
  ⟨((Subfunctor.range ζ0).sheafify (fppfTopology S)).toFunctor,
    (isSheaf_iff_isSheaf_of_type _ _).2 (Subfunctor.sheafify_isSheaf (J := fppfTopology S)
      (G := Subfunctor.range ζ0)
      ((isSheaf_iff_isSheaf_of_type _ _).1 (RelativePicard.classSheafPresheaf_isSheaf f)))⟩

/-- The corestriction of a morphism to its image sheaf. -/
abbrev toImage : uliftYoneda.{u + 1}.obj Z ⟶
    ((Subfunctor.range ζ0).sheafify (fppfTopology S)).toFunctor :=
  Subfunctor.toRangeSheafify (fppfTopology S) ζ0

lemma toImage_ι : toImage f ζ0 ≫ Subfunctor.ι _ = ζ0 := rfl

lemma toImage_app_val (T : Over S) (x : (uliftYoneda.{u + 1}.obj Z).obj (op T)) :
    ((toImage f ζ0).app (op T) x).val = ζ0.app (op T) x := rfl

/-- Two morphisms with the same composite to the Picard class sheaf have the same corestriction
to the image sheaf. -/
lemma toImage_comp_eq {Y : Over S} {a b : Y ⟶ Z}
    (h : uliftYoneda.{u + 1}.map a ≫ ζ0 = uliftYoneda.{u + 1}.map b ≫ ζ0) :
    uliftYoneda.{u + 1}.map a ≫ toImage f ζ0 = uliftYoneda.{u + 1}.map b ≫ toImage f ζ0 := by
  apply (cancel_mono (Subfunctor.ι _)).1
  rw [Category.assoc, Category.assoc, toImage_ι]
  exact h

end Image

/-- **Kleiman's construction of the pieces of the Picard scheme.** Given the divisor scheme with
its Hilbert-polynomial pieces, linear systems, fppf quotients by flat proper equivalence relations
and base change of relative effective divisors, the pieces of the Picard class sheaf cut out by
the given opens are represented on locally noetherian tests by H-quasi-projective schemes. -/
theorem picardHilbertPiecesRepresentabilityReduction :
    PicardHilbertPiecesRepresentabilityReductionStatement.{u} := by
  intro hD hLS hQ hbc A _ _ X f 𝓛X hprop hflat hgi hε h𝓛X hcis κ θ U hU1 hU2 hU3 hU4 c m
  have := hprop
  have := hflat
  have := hgi
  have : LocallyOfFinitePresentation f := inferInstance
  obtain ⟨D, d, W, hdlfp, -, hcl, U', -, -, hpieces⟩ := hD A f 𝓛X hflat h𝓛X hcis
  have := hdlfp
  have : IsLocallyNoetherian D := LocallyOfFiniteType.isLocallyNoetherian d
  have hLW := isInvertible_LW f 𝓛X h𝓛X d W m
  set Z₀ : D.Opens := U D d (LW f 𝓛X h𝓛X d W m) c m with hZ₀
  -- Step 1: the open `Z₀` lies in the piece of the divisor scheme of Hilbert polynomial `θ c m`.
  have hle : Z₀ ≤ U' (θ c m) := by
    intro z hz
    obtain ⟨_, ⟨V, hV, rfl⟩, hzV, hVZ⟩ :=
      D.isBasis_affineOpens.exists_subset_of_mem_open hz Z₀.2
    have : IsNoetherianRing Γ(D, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
    let g : Spec (CommRingCat.of Γ(D, V)) ⟶ D := hV.fromSpec
    have hg : Set.range g.base = (V : Set D) := hV.range_fromSpec
    have hgZ : g ⁻¹ᵁ Z₀ = ⊤ := by
      rw [eq_top_iff]
      intro x _
      exact hVZ (hg ▸ ⟨x, rfl⟩)
    have hJ := classifies_rel f d W hcl g rfl
    have hL := isInvertible_pullback (mapX f g rfl) hLW
    have htop : U _ (g ≫ d) ((Scheme.Modules.pullback (mapX f g rfl)).obj
        (LW f 𝓛X h𝓛X d W m)) c m = ⊤ := by
      rw [hU2' f hU2 g rfl _ hLW c m]
      exact hgZ
    obtain ⟨N, hN, hN0⟩ := exists_icl (0 : Group (Spec (CommRingCat.of Γ(D, V))))
    have hM := isInvertible_twist hL (isInvertible_pullback (pullback.fst f (g ≫ d)) h𝓛X) m
    have hiso := nonempty_iso_tensor_of_icl
      (isInvertible_lineBundle (EffectiveCartierDivisor.lineBundle ⟨_, hJ.1⟩)) hM
      (isInvertible_pullback (pullback.snd f (g ≫ d)) hN) (by
        rw [← dcl_eq_icl, dcl_comap_mapX f 𝓛X h𝓛X d W m hbc g rfl hJ.1,
          icl_twist_pt f 𝓛X h𝓛X d W m g rfl hM, icl_pullback _ _ hN, hN0, map_zero, add_zero])
    have hsub := ((hpieces (θ c m)).2 Γ(D, V) (g ≫ d) g rfl _ rfl).2 (by
      intro k _ _ sk
      exact hU4 Γ(D, V) (g ≫ d) _ hL c m htop _ hJ N hN hiso k sk)
    have hzg : z ∈ Set.range g.base := by
      rw [hg]
      exact hzV
    exact hsub hzg
  -- Step 2: `Z₀` is H-quasi-projective over `Spec A`.
  have hHQP : IsHQuasiProjective (Zo d Z₀).hom := by
    obtain ⟨n, i, hi, hqc, hc⟩ := (hpieces (θ c m)).1
    have := hi
    have := hqc
    refine ⟨n, D.homOfLE hle ≫ i, inferInstance, inferInstance, ?_⟩
    change (D.homOfLE hle ≫ i) ≫ _ = Z₀.ι ≫ d
    rw [Category.assoc, hc, ← Category.assoc, Scheme.homOfLE_ι]
  -- Step 3: the relation of linear equivalence on `Z₀` and the fppf quotient.
  obtain ⟨R, sR, tR, hsflat, hsprop, hrel, huniv⟩ :=
    exists_relation f 𝓛X h𝓛X d W m U hLS hcl hbc hε hU1 hU2 hU3 c Z₀ rfl
  obtain ⟨Q, π, e, hQHQP, hπe, hbij, hπflat, hπsurj, -, hπlfp⟩ :=
    hQ A (imageSheaf f (abelMap f 𝓛X h𝓛X d W m Z₀)) (Zo d Z₀) R
      (toImage f (abelMap f 𝓛X h𝓛X d W m Z₀)) sR tR hHQP
      (inferInstanceAs (Presheaf.IsLocallySurjective _
        (Subfunctor.toRangeSheafify _ (abelMap f 𝓛X h𝓛X d W m Z₀))))
      (toImage_comp_eq f _ hrel)
      (fun T _ x y hxy => huniv T x y (congrArg Subtype.val hxy))
      hsflat hsprop
  have := hπflat
  have := hπsurj
  have := hπlfp
  -- Step 4: the quotient represents the piece.
  refine ⟨Q, e ≫ Subfunctor.ι _, hQHQP, ?_⟩
  intro T _
  refine ⟨Subtype.val_injective.comp (hbij T).1, fun L => ?_⟩
  constructor
  · -- a class in the image has its open equal to `T`: pull back along the quotient map
    rintro ⟨qq, hq⟩
    let q : T ⟶ Q := qq.down
    let T₁ : Over (Spec (CommRingCat.of A)) := Over.mk (pullback.fst q.left π.left ≫ T.hom)
    have : IsLocallyNoetherian T₁.left :=
      LocallyOfFiniteType.isLocallyNoetherian (pullback.fst q.left π.left)
    let k₁ : T₁ ⟶ T := Over.homMk (pullback.fst q.left π.left) rfl
    let z : T₁ ⟶ Zo d Z₀ := Over.homMk (pullback.snd q.left π.left) (by
      change pullback.snd q.left π.left ≫ Z₀.ι ≫ d = pullback.fst q.left π.left ≫ T.hom
      rw [← Over.w q, ← Category.assoc (pullback.fst q.left π.left), pullback.condition,
        Category.assoc, Over.w π]
      rfl)
    have hkq : k₁ ≫ q = z ≫ π := Over.OverMorphism.ext pullback.condition
    have hqq : (uliftYoneda.{u + 1}.obj Q).map k₁.op qq =
        (uliftYoneda.{u + 1}.map π).app (op T₁) (ULift.up z) := ULift.ext _ _ hkq
    have hx1 : (RelativePicard.classSheafPresheaf f).map k₁.op
        (RelativePicard.sheafClassOf f T L) =
          (abelMap f 𝓛X h𝓛X d W m Z₀).app (op T₁) (ULift.up z) := by
      rw [← hq]
      have h1 := congrArg Subtype.val (NatTrans.naturality_apply e k₁.op qq)
      have h2 : (((schemeYoneda _).map π ≫ e).app (op T₁) (ULift.up z)).val =
          ((toImage f (abelMap f 𝓛X h𝓛X d W m Z₀)).app (op T₁) (ULift.up z)).val := by
        rw [hπe]
      rw [hqq] at h1
      exact h1.symm.trans h2
    rw [abelMap_app, sheafClassOf_eq_scl, map_scl] at hx1
    have hop := class_open f 𝓛X h𝓛X d W m U hε hU1 hU2 k₁ L _ _ hx1 c
    rw [← hZ₀, comap_preimage_ι_self] at hop
    exact eq_top_of_preimage_eq_top (pullback.fst q.left π.left) _ hop
  · -- a line bundle whose open is `T` has its class in the image: use its linear system
    intro htop
    have hrange : RelativePicard.sheafClassOf f T L ∈
        ((Subfunctor.range (abelMap f 𝓛X h𝓛X d W m Z₀)).sheafify
          (fppfTopology _)).obj (op T) := by
      have hL := isInvertible_tr f T L
      have hM := isInvertible_twist hL (isInvertible_pullback (pullback.fst f T.hom) h𝓛X) m
      obtain ⟨Λ, l, WΛ, NΛ, -, hN, ⟨eΛ⟩, -, -, h6⟩ :=
        hLS T.left (pullback.snd f T.hom) inferInstance inferInstance inferInstance _ hM
      obtain ⟨hlf, hlfp, hls⟩ := flat_of_top f 𝓛X m U hU3 _ _ hL c htop l h6
      have := hlf
      have := hlfp
      have := hls
      have : IsLocallyNoetherian Λ := LocallyOfFiniteType.isLocallyNoetherian l
      obtain ⟨y, wy, -, hy⟩ := linsys_class f 𝓛X h𝓛X d W m hcl hbc l WΛ _ hL NΛ hN eΛ
      let T' : Over (Spec (CommRingCat.of A)) := Over.mk (l ≫ T.hom)
      have : IsLocallyNoetherian T'.left := LocallyOfFiniteType.isLocallyNoetherian l
      let k : T' ⟶ T := Over.homMk l rfl
      have hk : scl f T' (Group.pullback ((relativeSpace f).map k) L.classOf) =
          scl f T' (ab f 𝓛X h𝓛X d W m T' y wy) := by
        rw [pb_relativeSpace_map f k L hL, ab]
        exact ((scl_sym_eq_iff f hε T' _ _).2 ⟨icl NΛ hN, hy⟩).symm
      have hop := class_open f 𝓛X h𝓛X d W m U hε hU1 hU2 k L y wy hk c
      rw [← hZ₀] at hop
      rw [show k.left = l from rfl, htop, Scheme.Hom.preimage_top] at hop
      let y' : Λ ⟶ Z₀ :=
        IsOpenImmersion.lift Z₀.ι y (range_subset_of_preimage_eq_top y Z₀ hop.symm)
      have hy' : y' ≫ Z₀.ι = y := IsOpenImmersion.lift_fac _ _ _
      let z : T' ⟶ Zo d Z₀ := Over.homMk y' (by
        change y' ≫ Z₀.ι ≫ d = l ≫ T.hom
        rw [← Category.assoc, hy', wy])
      have hab : ∀ (y₁ : T'.left ⟶ D) (w₁ : y₁ ≫ d = T'.hom), y₁ = y →
          ab f 𝓛X h𝓛X d W m T' y₁ w₁ = ab f 𝓛X h𝓛X d W m T' y wy := by
        rintro _ _ rfl
        rfl
      refine mem_fppf_over _ l ⟨ULift.up z, ?_⟩
      change (abelMap f 𝓛X h𝓛X d W m Z₀).app (op T') (ULift.up z) =
        (RelativePicard.classSheafPresheaf f).map k.op (RelativePicard.sheafClassOf f T L)
      rw [abelMap_app, sheafClassOf_eq_scl, map_scl, hk]
      exact congrArg (scl f T') (hab _ _ hy')
    obtain ⟨a, ha⟩ := (hbij T).2 ⟨_, hrange⟩
    exact ⟨a, congrArg Subtype.val ha⟩

end Langlands.AlgebraicGeometry.Picard.PicardHilbertPiecesReduction
