import Langlands.GroupScheme.Rational.RealCompactMaximalTorusConjugacyStatement
import Langlands.GroupScheme.Reductive.SelfAdjointRealizationProof
import Langlands.GroupScheme.Reductive.RationalPointDensityProof
import Langlands.GroupScheme.Reductive.FieldExtensionProof
import Langlands.Global.InfinitePlaceMatrixRealization
import Langlands.Group.MatrixPolarCompact
import Langlands.GroupScheme.Absolute.MaximalTorusConjugacyProof
import Langlands.GroupScheme.Torus.MaximalBaseChangeProof
import Langlands.GroupScheme.Rational.SplitRankTransport
import Langlands.GroupScheme.Rational.PointContainmentFromDensity
import Langlands.GroupScheme.Rational.SubgroupConjugacyDescent
import Langlands.GroupScheme.ClosedSubgroupMonomorphism
import Langlands.AlgebraicGeometry.PointTopology.SmoothSeparablyClosedDensity

/-! # Maximal-torus conjugacy for compact real semisimple groups -/

noncomputable section

open CategoryTheory AlgebraicGeometry Matrix
open Langlands.AlgebraicGeometry.PointTopology
open Langlands.Group.AlgebraicMatrixPowers Langlands.Group.AlgebraicPolar
open Langlands.Group.FormSelfAdjointMean
open scoped CategoryTheory.MonObj ComplexOrder

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false

private theorem exists_unitary_conjugator {n : Type} [Fintype n] [DecidableEq n]
    (A H K : Subgroup (GL n ℂ)) (hA : IsPolynomiallyDefined A)
    (hH : IsPolynomiallyDefined H) (hstarA : ∀ q ∈ A, star q ∈ A)
    (hstarH : ∀ q ∈ H, star q ∈ H) (hstarK : ∀ q ∈ K, star q ∈ K)
    (g : GL n ℂ) (hg : g ∈ A) (hconj : ∀ x, x ∈ H ↔ g * x * g⁻¹ ∈ K) :
    ∃ u ∈ A, u.val ∈ Matrix.unitaryGroup n ℂ ∧
      ∀ x, x ∈ H ↔ u * x * u⁻¹ ∈ K := by
  have hstar_iff (L : Subgroup (GL n ℂ)) (hL : ∀ q ∈ L, star q ∈ L) (x : GL n ℂ) :
      star x ∈ L ↔ x ∈ L :=
    ⟨fun hx => by simpa only [star_star] using hL _ hx, hL x⟩
  have hconjStar (x : GL n ℂ) : x ∈ H ↔ (star g)⁻¹ * x * star g ∈ K := by
    have h := (hstar_iff H hstarH x).symm.trans
      ((hconj (star x)).trans (hstar_iff K hstarK _).symm)
    simpa only [star_mul, star_inv, star_star, mul_assoc] using h
  let q := star g * g
  have hq : q.val.PosDef := posDef_star_mul_self g
  have hqN : q ∈ Subgroup.normalizer (H : Set (GL n ℂ)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine (hconj x).trans ?_
    have he : (star g)⁻¹ * (q * x * q⁻¹) * star g = g * x * g⁻¹ := by
      dsimp [q]
      group
    rw [← he]
    exact (hconjStar _).symm
  let a := positivePower q hq (1 / 2)
  have haA : a ∈ A := positivePower_mem A hA q hq (A.mul_mem (hstarA g hg) hg) _
  have haN : a ∈ Subgroup.normalizer (H : Set (GL n ℂ)) :=
    positivePower_mem _ (isPolynomiallyDefined_normalizer H hH) q hq hqN _
  refine ⟨g * a⁻¹, A.mul_mem hg (A.inv_mem haA), ?_, ?_⟩
  · apply (Units.mul_inv_mem_unitary g a).mpr
    rw [star_eq_self_of_posDef (positivePower_posDef q hq _), positivePower_half_sq]
  · intro x
    have h := ((Subgroup.mem_normalizer_iff.mp (inv_mem haN)) x).trans (hconj _)
    simpa only [_root_.mul_inv_rev, inv_inv, mul_assoc] using h

private theorem section_eq_zero_of_dense_realPoints
    {G : GroupScheme (Spec (CommRingCat.of ℝ))} [IsReduced G.X.left]
    (hd : HasDenseRationalPoints ℝ G.X) (s : Γ(G.X.left, ⊤))
    (h : ∀ x : G.affinePoints (CommAlgCat.of ℝ ℝ), G.affinePointEvaluation _ x s = 0) :
    s = 0 := by
  by_contra hs
  have hne : (G.X.left.basicOpen s : Set G.X.left).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro he
    apply hs
    rw [← basicOpen_eq_bot_iff]
    exact SetLike.coe_injective (he.trans TopologicalSpace.Opens.coe_bot.symm)
  obtain ⟨_, hx, hy⟩ := hd.inter_open_nonempty _ (G.X.left.basicOpen s).isOpen hne
  obtain ⟨p, z, rfl⟩ := Set.mem_iUnion.mp hy
  have hz : p.left.appTop s = 0 := by
    apply (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of ℝ)).hom).1
    rw [map_zero]
    change (p.left.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of ℝ)).hom).hom s = 0
    have hp := h (rationalPointEquiv ℝ G.X p)
    change ((rationalPointEquiv ℝ G.X p).left.appTop ≫
      (Scheme.ΓSpecIso (CommRingCat.of ℝ)).hom).hom s = 0 at hp
    rwa [rationalPointEquiv_left] at hp
  have hmem : z ∈ p.left ⁻¹ᵁ G.X.left.basicOpen s := hx
  rw [Scheme.preimage_basicOpen_top, hz, Scheme.basicOpen_zero] at hmem
  exact hmem

private theorem star_eq_inv_of_compact_realPoints
    {G : GroupScheme (Spec (CommRingCat.of ℝ))} [IsAffine G.X.left]
    {d : ℕ} (ρ : MatrixRepresentation G (Fin d))
    (hc : letI := rationalPointTopology ℝ G.X; IsCompact (Set.univ : Set (rationalPoints G)))
    (hstar : ∀ q ∈ (ρ.affineMatrix (CommAlgCat.of ℝ ℝ)).range,
      star q ∈ (ρ.affineMatrix (CommAlgCat.of ℝ ℝ)).range)
    (q : GL (Fin d) ℝ) (hq : q ∈ (ρ.affineMatrix (CommAlgCat.of ℝ ℝ)).range) :
    star q = q⁻¹ := by
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology ℝ G.X
  let : TopologicalSpace (G.affinePoints (CommAlgCat.of ℝ ℝ)) :=
    G.affinePointsTopologicalSpace _
  let e := rationalPointsAffineHomeomorph G
  have hp : IsCompact (e '' (Set.univ : Set (rationalPoints G))) := hc.image e.continuous
  rw [Set.image_univ, e.surjective.range_eq] at hp
  have hm : IsCompact ((ρ.affineMatrix (CommAlgCat.of ℝ ℝ)).range : Set (GL (Fin d) ℝ)) := by
    change IsCompact (Set.range (ρ.affineMatrix (CommAlgCat.of ℝ ℝ)))
    rw [← Set.image_univ]
    exact hp.image (ρ.continuous_affineMatrix (CommAlgCat.of ℝ ℝ))
  exact eq_inv_of_mul_eq_one_left (Langlands.Group.MatrixPolarCompact.eq_one_of_posSemidef
    _ hm _ (Subgroup.mul_mem _ (hstar q hq) hq) (posDef_star_mul_self q).posSemidef)

private theorem star_eq_conj_inv_of_compact_realPoints
    {G : GroupScheme (Spec (CommRingCat.of ℝ))} [IsAffine G.X.left] [IsReduced G.X.left]
    {d : ℕ} (ρ : MatrixRepresentation G (Fin d)) (hd : HasDenseRationalPoints ℝ G.X)
    (hc : letI := rationalPointTopology ℝ G.X; IsCompact (Set.univ : Set (rationalPoints G)))
    (hstar : ∀ q ∈ (ρ.affineMatrix (CommAlgCat.of ℝ ℝ)).range,
      star q ∈ (ρ.affineMatrix (CommAlgCat.of ℝ ℝ)).range)
    (q : GL (Fin d) ℂ) (hq : q ∈ (ρ.affineMatrix (CommAlgCat.of ℝ ℂ)).range) :
    star q = conjGL q⁻¹ := by
  obtain ⟨x, rfl⟩ := hq
  apply Units.ext
  ext i j
  let R := CommRingCat.of ℝ
  let n := Fin d
  let s := GeneralLinear.entrySection n R j i - GeneralLinear.inverseEntrySection n R i j
  have heval (S : CommAlgCat R) (y : G.affinePoints S) :
      G.affinePointEvaluation S y (ρ.hom.hom.left.appTop s) =
        ρ.affineMatrix S y j i - (ρ.affineMatrix S y)⁻¹ i j := by
    rw [← affinePointEvaluation_postcomp]
    rw [show s = GeneralLinear.entrySection n R j i -
      GeneralLinear.inverseEntrySection n R i j from rfl, map_sub]
    exact congrArg₂ (fun a b : S => a - b)
      (GeneralLinear.affinePointsEquiv_entry_evaluation n R S (y ≫ ρ.hom.hom) j i).symm
      (GeneralLinear.affinePointsEquiv_inverseEntry_evaluation n R S (y ≫ ρ.hom.hom) i j).symm
  have hs : ρ.hom.hom.left.appTop s = 0 := by
    apply section_eq_zero_of_dense_realPoints hd
    intro y
    rw [heval, sub_eq_zero]
    have hy := star_eq_inv_of_compact_realPoints ρ hc hstar _ ⟨y, rfl⟩
    simpa only [Units.coe_star, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
      star_trivial] using congrArg (fun M : GL n ℝ => M i j) hy
  have hx := heval (CommAlgCat.of ℝ ℂ) x
  rw [hs, map_zero] at hx
  change star (ρ.affineMatrix (CommAlgCat.of ℝ ℂ) x j i) =
    star ((ρ.affineMatrix (CommAlgCat.of ℝ ℂ) x)⁻¹ i j)
  rw [sub_eq_zero.mp hx.symm]

private theorem conjGL_affineMatrix {G : GroupScheme (Spec (CommRingCat.of ℝ))}
    {d : ℕ} (ρ : MatrixRepresentation G (Fin d)) (x : G.affinePoints (CommAlgCat.of ℝ ℂ)) :
    ρ.affineMatrix (CommAlgCat.of ℝ ℂ) (G.affinePointAut Complex.conjAe x) =
      conjGL (ρ.affineMatrix (CommAlgCat.of ℝ ℂ) x) :=
  ρ.affineMatrix_naturality (CommAlgCat.ofHom Complex.conjAe.toAlgHom) x

set_option maxHeartbeats 1000000 in
private theorem star_mem_restricted_range
    {G H : GroupScheme (Spec (CommRingCat.of ℝ))} {d : ℕ}
    (ρ : MatrixRepresentation G (Fin d)) (i : H ⟶ G)
    (horth : ∀ q ∈ (ρ.affineMatrix (CommAlgCat.of ℝ ℂ)).range, star q = conjGL q⁻¹)
    (q : GL (Fin d) ℂ) (hq : q ∈ ((ρ.restrict i).affineMatrix (CommAlgCat.of ℝ ℂ)).range) :
    star q ∈ ((ρ.restrict i).affineMatrix (CommAlgCat.of ℝ ℂ)).range := by
  obtain ⟨x, rfl⟩ := hq
  let C := CommAlgCat.of ℝ ℂ
  let f := (ρ.restrict i).affineMatrix C
  change star (f x) ∈ f.range
  have hmem : f x ∈ (ρ.affineMatrix C).range :=
    ⟨x ≫ i.hom.hom, (ρ.affineMatrix_restrict i C x).symm⟩
  refine ⟨H.affinePointAut Complex.conjAe x⁻¹, ?_⟩
  calc
    f (H.affinePointAut Complex.conjAe x⁻¹) = conjGL (f x⁻¹) :=
      conjGL_affineMatrix (ρ.restrict i) x⁻¹
    _ = conjGL (f x)⁻¹ := congrArg conjGL (map_inv f x)
    _ = star (f x) := (horth _ hmem).symm

private abbrev pointRange {k : Type} [Field k]
    {H G : GroupScheme (Spec (CommRingCat.of k))} (i : H ⟶ G) :
    Subgroup (rationalPoints G) :=
  (SubgroupFunctor.range i).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k))))

private theorem mem_pointRange_innerIso {k : Type} [Field k]
    {H G : GroupScheme (Spec (CommRingCat.of k))} (i : H ⟶ G) (g x : rationalPoints G) :
    g * x * g⁻¹ ∈ pointRange (i ≫ (G.innerIso g).hom) ↔ x ∈ pointRange i := by
  have he (y : rationalPoints H) :
      rationalPoints.map (i ≫ (G.innerIso g).hom) y =
        g * (rationalPoints.map i y) * g⁻¹ := by
    rw [rationalPoints.map_apply, Grp.comp_hom_hom, ← Category.assoc, comp_innerIso_hom,
      constantPoint_self, rationalPoints.map_apply]
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨y, (MulAut.conj g).injective ?_⟩
    change g * (rationalPoints.map i y) * g⁻¹ = g * x * g⁻¹
    exact (he y).symm.trans hy
  · rintro ⟨y, rfl⟩
    exact ⟨y, he y⟩

private theorem conjugates_map {P Q : Type} [Group P] [Group Q]
    (f : P →* Q) (H K : Subgroup P) (g : P) (h : ∀ x, x ∈ H ↔ g * x * g⁻¹ ∈ K)
    (x : Q) : x ∈ H.map f ↔ f g * x * (f g)⁻¹ ∈ K.map f := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨_, (h y).mp hy, by rw [map_mul, map_mul, map_inv]⟩
  · rintro ⟨y, hy, he⟩
    have hc : g * (g⁻¹ * y * g) * g⁻¹ = y := by group
    refine ⟨g⁻¹ * y * g, (h _).mpr (hc.symm ▸ hy), ?_⟩
    rw [map_mul, map_mul, map_inv, he]
    group

open GaloisPointComparison

private def complexMatrixHom {G : GroupScheme (Spec (CommRingCat.of ℝ))} {d : ℕ}
    (ρ : MatrixRepresentation G (Fin d)) :
    rationalPoints (baseChanged ℝ ℂ G) →* GL (Fin d) ℂ :=
  (ρ.affineMatrix (CommAlgCat.of ℝ ℂ)).comp (baseChangeCoeffEquiv ℝ ℂ G).toMonoidHom

private theorem complexMatrixHom_range {G : GroupScheme (Spec (CommRingCat.of ℝ))} {d : ℕ}
    (ρ : MatrixRepresentation G (Fin d)) :
    (complexMatrixHom ρ).range = (ρ.affineMatrix (CommAlgCat.of ℝ ℂ)).range := by
  ext u
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨baseChangeCoeffEquiv ℝ ℂ G x, rfl⟩
  · rintro ⟨x, rfl⟩
    exact ⟨(baseChangeCoeffEquiv ℝ ℂ G).symm x,
      congrArg (ρ.affineMatrix (CommAlgCat.of ℝ ℂ))
        ((baseChangeCoeffEquiv ℝ ℂ G).apply_symm_apply x)⟩

private theorem complexMatrixHom_injective {G : GroupScheme (Spec (CommRingCat.of ℝ))} {d : ℕ}
    (ρ : MatrixRepresentation G (Fin d)) (hρ : IsClosedSubgroup ρ) :
    Function.Injective (complexMatrixHom ρ) := by
  let : Mono ρ.hom.hom := hρ.mono_overHom
  intro x y h
  apply (baseChangeCoeffEquiv ℝ ℂ G).injective
  apply (cancel_mono ρ.hom.hom).mp
  exact (GeneralLinear.affinePointsEquiv (Fin d) (CommRingCat.of ℝ) (CommAlgCat.of ℝ ℂ)).injective h

set_option maxHeartbeats 1000000 in
private theorem map_pointRange_eq_affineMatrix_range
    {G H : GroupScheme (Spec (CommRingCat.of ℝ))} {d : ℕ}
    (ρ : MatrixRepresentation G (Fin d)) (i : H ⟶ G) :
    (pointRange ((GroupScheme.baseChange (baseMap ℝ ℂ)).map i)).map (complexMatrixHom ρ) =
      ((ρ.restrict i).affineMatrix (CommAlgCat.of ℝ ℂ)).range := by
  let iC := (GroupScheme.baseChange (baseMap ℝ ℂ)).map i
  let e := baseChangeCoeffEquiv ℝ ℂ H
  let f := (ρ.restrict i).affineMatrix (CommAlgCat.of ℝ ℂ)
  change (pointRange iC).map (complexMatrixHom ρ) = f.range
  have he (x : rationalPoints (baseChanged ℝ ℂ H)) :
      complexMatrixHom ρ (rationalPoints.map iC x) = f (e x) := by
    change ρ.affineMatrix _ (baseChangeCoeffEquiv ℝ ℂ G (rationalPoints.map iC x)) = f (e x)
    rw [baseChangeCoeffEquiv_map, affinePointsTarget_apply]
    exact (ρ.affineMatrix_restrict i _ (e x)).symm
  ext a
  constructor
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨e x, (he x).symm⟩
  · rintro ⟨x, rfl⟩
    exact ⟨rationalPoints.map iC (e.symm x), ⟨e.symm x, rfl⟩,
      (he (e.symm x)).trans (congrArg f (e.apply_symm_apply x))⟩

set_option maxHeartbeats 2500000 in
/-- Maximal tori of a compact real semisimple group are conjugate by a real
point, with equality of their full subgroup functors. -/
theorem realCompactMaximalTorusConjugacy : RealCompactMaximalTorusConjugacyStatement := by
  intro G hG
  let : IsAffineHom G.X.hom := hG.isConnectedReductive.isAffineHom
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : Smooth G.X.hom := hG.isConnectedReductive.smooth
  let : IsReduced G.X.left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field ℝ _ G.X.hom
  intro hc T T' j j' hj hj'
  obtain ⟨d, ρ, hρ, hstar⟩ :=
    SelfAdjointRealization.connectedReductiveSelfAdjointRealizationStatement
      ℝ G hG.isConnectedReductive
  let C := CommAlgCat.of ℝ ℂ
  let A := (ρ.affineMatrix C).range
  let H := ((ρ.restrict j).affineMatrix C).range
  let K := ((ρ.restrict j').affineMatrix C).range
  let : IsClosedImmersion ρ.hom.hom.left := hρ
  let : IsClosedImmersion (ρ.restrict j).hom.hom.left := hj.2.1.comp hρ
  -- Extend the real orthogonality identities to the complex matrix images.
  have horth (q : GL (Fin d) ℂ) (hq : q ∈ A) : star q = conjGL q⁻¹ :=
    star_eq_conj_inv_of_compact_realPoints ρ
      (reductiveRationalPointDensity ℝ G hG.isConnectedReductive) hc hstar q hq
  have hstarA : ∀ q ∈ A, star q ∈ A := by
    rintro q ⟨x, rfl⟩
    refine ⟨G.affinePointAut Complex.conjAe x⁻¹, ?_⟩
    rw [conjGL_affineMatrix, map_inv]
    exact (horth _ ⟨x, rfl⟩).symm
  -- Obtain a complex conjugator and transport it through the faithful representation.
  let b := baseMap ℝ ℂ
  let GC := baseChanged ℝ ℂ G
  let TC := (CommGroupScheme.baseChange b).obj T
  let TC' := (CommGroupScheme.baseChange b).obj T'
  let jC : TC.toGrp ⟶ GC := (GroupScheme.baseChange b).map j
  let jC' : TC'.toGrp ⟶ GC := (GroupScheme.baseChange b).map j'
  have hGC : IsConnectedReductive GC :=
    connectedReductiveFieldExtensionStatement ℝ ℂ G hG.isConnectedReductive
  let : Smooth GC.X.hom := hGC.smooth
  let : IsAffineHom GC.X.hom := hGC.isAffineHom
  let : ConnectedSpace GC.X.left := hGC.connectedSpace
  have hjC : IsMaximalTorus jC := (maximalTorusBaseChange ℝ ℂ G T j hj.1 hj.2.1).mp hj
  have hjC' : IsMaximalTorus jC' := (maximalTorusBaseChange ℝ ℂ G T' j' hj'.1 hj'.2.1).mp hj'
  obtain ⟨g, e, he⟩ := maximalTorusConjugacy ℂ GC TC TC' jC jC' hjC hjC'
  let eG : TC.toGrp ≅ TC'.toGrp :=
    { hom := CommGroupScheme.groupHom e.hom
      inv := CommGroupScheme.groupHom e.inv
      hom_inv_id := congrArg Additive.toMul e.hom_inv_id
      inv_hom_id := congrArg Additive.toMul e.inv_hom_id }
  have hcomplexRange :
      SubgroupFunctor.range (jC ≫ (GC.innerIso g).hom) = SubgroupFunctor.range jC' :=
    (congrArg SubgroupFunctor.range he).trans (SubgroupFunctor.range_iso_comp eG jC')
  have hcomplexPts (x : rationalPoints GC) : x ∈ pointRange jC ↔ g * x * g⁻¹ ∈ pointRange jC' := by
    change _ ↔ g * x * g⁻¹ ∈ (SubgroupFunctor.range jC').carrier _
    rw [← hcomplexRange]
    exact (mem_pointRange_innerIso jC g x).symm
  let f := complexMatrixHom ρ
  have hf : Function.Injective f := complexMatrixHom_injective ρ hρ
  have hfRange : f.range = A := complexMatrixHom_range ρ
  have hH : (pointRange jC).map f = H := map_pointRange_eq_affineMatrix_range ρ j
  have hK : (pointRange jC').map f = K := map_pointRange_eq_affineMatrix_range ρ j'
  have hg : f g ∈ A := hfRange ▸ ⟨g, rfl⟩
  have hmatrix (x : GL (Fin d) ℂ) : x ∈ H ↔ f g * x * (f g)⁻¹ ∈ K := by
    rw [← hH, ← hK]
    exact conjugates_map f _ _ g hcomplexPts x
  obtain ⟨u, hu, hunit, huconj⟩ := exists_unitary_conjugator A H K
    (ρ.affineMatrix_range_isPolynomiallyDefined ℂ)
    ((ρ.restrict j).affineMatrix_range_isPolynomiallyDefined ℂ)
    hstarA (star_mem_restricted_range ρ j horth) (star_mem_restricted_range ρ j' horth)
    (f g) hg hmatrix
  -- The adjusted matrix is fixed by complex conjugation.
  have hunit' : star u * u = 1 := Units.ext (Unitary.star_mul_self_of_mem hunit)
  have hreal : conjGL u = u := by
    have h := (horth u hu).symm.trans (eq_inv_of_mul_eq_one_left hunit')
    rw [map_inv] at h
    exact inv_injective h
  have huf : u ∈ f.range := hfRange.symm ▸ hu
  obtain ⟨uC, huC⟩ := huf
  have hfixed (σ : ℂ ≃ₐ[ℝ] ℂ) : rationalConjugate ℝ ℂ G σ uC = uC := by
    rcases Complex.real_algHom_eq_id_or_conj σ.toAlgHom with hσ | hσ
    · have heq : σ = 1 := AlgEquiv.coe_toAlgHom_injective hσ
      rw [heq, rationalConjugate_one]
    · have heq : σ = Complex.conjAe := AlgEquiv.coe_toAlgHom_injective hσ
      apply hf
      change ρ.affineMatrix C (baseChangeCoeffEquiv ℝ ℂ G (rationalConjugate ℝ ℂ G σ uC)) = f uC
      rw [baseChangeCoeffEquiv_rationalConjugate, heq]
      change ρ.affineMatrix C (G.affinePointAut Complex.conjAe
        (baseChangeCoeffEquiv ℝ ℂ G uC)) = f uC
      rw [conjGL_affineMatrix]
      change conjGL (f uC) = f uC
      rwa [huC]
  have huPts (x : rationalPoints GC) :
      x ∈ pointRange jC ↔ uC * x * uC⁻¹ ∈ pointRange jC' := by
    have h := huconj (f x)
    rw [← hH, ← hK, ← huC, ← map_inv f, ← map_mul, ← map_mul,
      Subgroup.mem_map_iff_mem hf, Subgroup.mem_map_iff_mem hf] at h
    exact h
  have hpointEq : pointRange (jC ≫ (GC.innerIso uC).hom) = pointRange jC' := by
    ext y
    have hy : uC * (uC⁻¹ * y * uC) * uC⁻¹ = y := by group
    rw [← hy, mem_pointRange_innerIso]
    exact huPts _
  -- Density identifies the closed subgroup functors before fpqc descent.
  let : Smooth TC.X.hom := hjC.1.smooth
  let : Smooth TC'.X.hom := hjC'.1.smooth
  let : IsReduced TC.X.left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field ℂ _ TC.X.hom
  let : IsReduced TC'.X.left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field ℂ _ TC'.X.hom
  have hCeq : SubgroupFunctor.range (jC ≫ (GC.innerIso uC).hom) = SubgroupFunctor.range jC' :=
    le_antisymm
      (SubgroupFunctor.range_le_of_dense_rationalPoints
        (hasDenseRationalPoints_of_smooth_of_isSepClosed ℂ TC.X) hjC'.2.1 hpointEq.le)
      (SubgroupFunctor.range_le_of_dense_rationalPoints
        (hasDenseRationalPoints_of_smooth_of_isSepClosed ℂ TC'.X)
        (hjC.2.1.comp_iso (GC.innerIso uC)) hpointEq.ge)
  let : Algebra.IsQuadraticExtension ℝ ℂ :=
    { toFree := inferInstance, finrank_eq_two' := Complex.finrank_real_complex }
  let v := rationalPointOfGaloisFixed ℝ ℂ G uC hfixed
  have hv : baseChangeBasePoint b G v = uC :=
    baseChangeBasePoint_rationalPointOfGaloisFixed ℝ ℂ G uC hfixed
  have hfpqc := fieldExtension_fpqc ℝ ℂ
  let : Surjective b := hfpqc.1
  let : Flat b := hfpqc.2.1
  let : QuasiCompact b := hfpqc.2.2
  let : Mono (j ≫ (G.innerIso v).hom).hom.hom := (hj.2.1.comp_iso (G.innerIso v)).mono_overHom
  let : Mono j'.hom.hom := hj'.2.1.mono_overHom
  refine ⟨v, SubgroupFunctor.range_eq_of_baseChange_eq b _ _ ?_⟩
  rw [← SubgroupFunctor.range_baseChangeHom, ← SubgroupFunctor.range_baseChangeHom,
    Functor.map_comp, baseChange_innerIso_hom, hv]
  exact hCeq

end Langlands.GroupScheme
