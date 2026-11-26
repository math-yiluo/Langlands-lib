import Langlands.GroupScheme.Dynamic.OpenProductContraction
import Langlands.GroupScheme.Dynamic.NormalizedLimits
import Langlands.GroupScheme.Absolute.OppositeCellProof

/-! # Opposite factors of a contracting subgroup for two commuting cocharacters -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme.Dynamic

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}

local notation "S" => Spec (CommRingCat.of k)

private theorem exists_factor_at_fieldPoint {K : Type u} [Field K] {f : Spec (.of K) ⟶ S}
    {U : Over S} (j : U ⟶ G.X) [IsOpenImmersion j.left]
    (g : Over.mk f ⟶ G.X) (hg : g.left (⊥ : PrimeSpectrum K) ∈ j.left.opensRange) :
    ∃ a : Over.mk f ⟶ U, a ≫ j = g := by
  have hr : Set.range g.left ⊆ Set.range j.left := by
    rintro _ ⟨x, rfl⟩
    have hx : x = (⊥ : PrimeSpectrum K) := Subsingleton.elim (α := PrimeSpectrum K) _ _
    rwa [hx]
  refine ⟨Over.homMk (IsOpenImmersion.lift j.left g.left hr) ?_,
    Over.OverMorphism.ext (IsOpenImmersion.lift_fac _ _ _)⟩
  rw [← Over.w j, ← Category.assoc, IsOpenImmersion.lift_fac, Over.w]

private theorem genericPoint_mem_open {K : Type u} [Field K]
    (W : TopologicalSpace.Opens (PrimeSpectrum (Polynomial K)))
    (h : (W : Set (PrimeSpectrum (Polynomial K))).Nonempty) :
    (⊥ : PrimeSpectrum (Polynomial K)) ∈ W := by
  have hgen : IsGenericPoint (⊥ : PrimeSpectrum (Polynomial K)) Set.univ := by
    rw [isGenericPoint_def, ← PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure,
      PrimeSpectrum.vanishingIdeal_singleton, ← PrimeSpectrum.zeroLocus_singleton_zero]
    rfl
  exact (hgen.mem_open_set_iff W.isOpen).2 (by simpa using h)

/-- An open immersion stable under a cocharacter and containing the identity
contains every identity-limit orbit extension, over an arbitrary test scheme. -/
theorem exists_lift_contraction_stableOpen
    (χ : (Gm S).toGrp ⟶ G) {U T : Over S} (j : U ⟶ G.X)
    [IsOpenImmersion j.left] (hj : IsCocharacterStable χ j)
    (z : Over.mk (𝟙 S) ⟶ U) (hz : z ≫ j = 1)
    {g : T ⟶ G.X} {e : T ⊗ AffineLine.scheme S ⟶ G.X}
    (he : IsOrbitExtension χ g e) (he0 : evalZero e = 1) :
    ∃ e' : T ⊗ AffineLine.scheme S ⟶ U, e' ≫ j = e := by
  have hrange : Set.range e.left ⊆ Set.range j.left := by
    rintro _ ⟨x, rfl⟩
    -- The coordinate of a residue-field point is zero or a unit.
    let f := (T ⊗ AffineLine.scheme S).left.fromSpecResidueField x ≫
      (T ⊗ AffineLine.scheme S).hom
    let b : Over.mk f ⟶ T ⊗ AffineLine.scheme S :=
      Over.homMk ((T ⊗ AffineLine.scheme S).left.fromSpecResidueField x) rfl
    let bT := b ≫ fst T (AffineLine.scheme S)
    let bx := b ≫ snd T (AffineLine.scheme S)
    have hb : b = lift bT bx := by
      apply CartesianMonoidalCategory.hom_ext <;> simp [bT, bx]
    let K := (T ⊗ AffineLine.scheme S).left.residueField x
    -- Work on the affine line over the residue field of the product point.
    let eK := (bT ▷ AffineLine.scheme S) ≫ e
    have heK : IsOrbitExtension χ (bT ≫ g) eK := by
      unfold IsOrbitExtension at he ⊢
      dsimp only [eK]
      rw [whisker_exchange_assoc, he, whiskerRight_orbit]
    have heK0 : evalZero eK = 1 := by
      dsimp only [eK]
      rw [evalZero_whiskerRight, he0, MonObj.comp_one]
    let p := AffineLine.polynomialPoint f ≫ eK
    have hp0 : (AffineLine.polynomialZero f ≫ p) = 1 := by
      dsimp only [p]
      rw [← Category.assoc, AffineLine.polynomialZero_comp_polynomialPoint]
      exact heK0
    have hzero : (AffineLine.polynomialZero f ≫ p).left (⊥ : PrimeSpectrum K) ∈
        j.left.opensRange := by
      rw [hp0]
      let zK : Over.mk f ⟶ U := toUnit (Over.mk f) ≫ z
      have hzK : zK ≫ j = 1 := by dsimp only [zK]; rw [Category.assoc, hz, MonObj.comp_one]
      rw [← hzK]
      exact ⟨zK.left (⊥ : PrimeSpectrum K), rfl⟩
    have hgeneric : p.left (⊥ : PrimeSpectrum (Polynomial K)) ∈ j.left.opensRange := by
      apply genericPoint_mem_open (p.left ⁻¹ᵁ j.left.opensRange)
      exact ⟨(AffineLine.polynomialZero f).left (⊥ : PrimeSpectrum K), hzero⟩
    have hLaurent :
        (AffineLine.laurentInclusion f).left (⊥ : PrimeSpectrum (LaurentPolynomial K)) =
          (⊥ : PrimeSpectrum (Polynomial K)) := by
      apply PrimeSpectrum.ext
      let u : Polynomial K →+* LaurentPolynomial K := Polynomial.toLaurent
      exact (RingHom.ker_eq_comap_bot u).symm.trans
        ((RingHom.ker_eq_bot_iff_eq_zero u).2
          (fun a ha => Polynomial.toLaurent_injective (ha.trans (map_zero _).symm)))
    let L := AffineLine.laurentScheme f
    let t : PrimeSpectrum (LaurentPolynomial K) := ⊥
    let R := L.left.residueField t
    let fL : Spec (CommRingCat.of R) ⟶ S := L.left.fromSpecResidueField t ≫ L.hom
    let r : Over.mk fL ⟶ L := Over.homMk (L.left.fromSpecResidueField t) rfl
    let a := r ≫ AffineLine.laurentPoint f ≫ snd (Over.mk f) (Gm S).X
    let d := r ≫ AffineLine.laurentPoint f ≫ fst (Over.mk f) (Gm S).X
    have horbit : r ≫ AffineLine.laurentInclusion f ≫ p =
        (a ≫ χ.hom.hom) * (d ≫ bT ≫ g) * (a ≫ χ.hom.hom)⁻¹ := by
      dsimp only [p]
      rw [AffineLine.laurentInclusion_comp_of_whiskerLeft f heK]
      simp only [a, d, orbit, Category.assoc, MonObj.comp_mul, GrpObj.comp_inv]
    have hgenLift : ∃ q : Over.mk fL ⟶ U,
        q ≫ j = (a ≫ χ.hom.hom) * (d ≫ bT ≫ g) * (a ≫ χ.hom.hom)⁻¹ := by
      rw [← horbit]
      apply exists_factor_at_fieldPoint j
      change p.left ((AffineLine.laurentInclusion f).left (r.left (⊥ : PrimeSpectrum R))) ∈ _
      have hres : r.left (⊥ : PrimeSpectrum R) = t := Scheme.fromSpecResidueField_apply _ _
      rw [hres, show t = (⊥ : PrimeSpectrum (LaurentPolynomial K)) from rfl, hLaurent]
      exact hgeneric
    obtain ⟨q, hq⟩ := (hj.factors_iff χ a (d ≫ bT ≫ g)).mp hgenLift
    have hgIn : (bT ≫ g).left (⊥ : PrimeSpectrum K) ∈ j.left.opensRange := by
      have hd : d.left (⊥ : PrimeSpectrum R) = (⊥ : PrimeSpectrum K) :=
        Subsingleton.elim (α := PrimeSpectrum K) _ _
      refine ⟨q.left (⊥ : PrimeSpectrum R), ?_⟩
      have h := congrArg (fun p : Over.mk fL ⟶ G.X => p.left (⊥ : PrimeSpectrum R)) hq
      simpa only [Over.comp_left, Scheme.Hom.comp_apply, hd] using h
    have hfull : ∀ y : Over.mk f ⟶ G.X, y.left (⊥ : PrimeSpectrum K) ∈ j.left.opensRange →
        ∃ q : Over.mk f ⟶ U, q ≫ j = y := exists_factor_at_fieldPoint j
    have hbe : ∃ q : Over.mk f ⟶ U, q ≫ j = b ≫ e := by
      by_cases hb0 : AffineLine.homEquiv (Over.mk f) bx = 0
      · have hbzero : b ≫ e = 1 := by
          rw [hb]
          have hEq : bx = toUnit (Over.mk f) ≫ AffineLine.zeroSection S := by
            apply (AffineLine.homEquiv _).injective
            rw [AffineLine.homEquiv_comp_zeroSection]
            exact hb0
          rw [hEq]
          have heval : lift bT (toUnit (Over.mk f) ≫ AffineLine.zeroSection S) ≫ e =
              bT ≫ evalZero e := by
            simp only [evalZero, ← Category.assoc, comp_lift, Category.comp_id, comp_toUnit]
          rw [heval, he0, MonObj.comp_one]
        refine ⟨toUnit (Over.mk f) ≫ z, ?_⟩
        rw [hbzero, Category.assoc, hz, MonObj.comp_one]
      · let i := Scheme.ΓSpecIso (CommRingCat.of K)
        let bₓ := AffineLine.homEquiv (Over.mk f) bx
        have hbx : i.hom bₓ ≠ 0 := by
          intro h
          apply hb0
          change bₓ = 0
          rw [← i.hom_inv_id_apply bₓ, h, map_zero]
        let ax := (Gm.pointsEquiv S (Over.mk f)).symm
          (Units.map i.inv.hom.toMonoidHom (Units.mk0 _ hbx))
        have hax : ax ≫ AffineLine.unitInclusion S = bx := by
          apply (AffineLine.homEquiv _).injective
          simp only [AffineLine.homEquiv_comp_unitInclusion, ax, MulEquiv.apply_symm_apply,
            Units.val_mk0, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass]
          exact i.hom_inv_id_apply bₓ
        have hact : b ≫ e = (ax ≫ χ.hom.hom) * (bT ≫ g) * (ax ≫ χ.hom.hom)⁻¹ := by
          rw [hb, ← hax, ← lift_whiskerLeft_assoc, he]
          simp only [orbit, MonObj.comp_mul, GrpObj.comp_inv, lift_fst_assoc, lift_snd_assoc]
        rw [hact]
        exact (hj.factors_iff χ ax _).mpr (hfull _ hgIn)
    obtain ⟨q', hq'⟩ := hbe
    refine ⟨q'.left (⊥ : PrimeSpectrum K), ?_⟩
    have hres : b.left (⊥ : PrimeSpectrum K) = x := Scheme.fromSpecResidueField_apply _ _
    simpa only [Over.comp_left, Scheme.Hom.comp_apply, hres] using
      congrArg (fun p : Over.mk f ⟶ G.X => p.left (⊥ : PrimeSpectrum K)) hq'
  exact ⟨Over.homMk (IsOpenImmersion.lift j.left e.left hrange) (by
    rw [← Over.w j, ← Category.assoc, IsOpenImmersion.lift_fac, Over.w]),
    Over.OverMorphism.ext (IsOpenImmersion.lift_fac _ _ _)⟩

/-- For two cocharacters in a common commutative group with the same centralizer,
the source radical is the ordered product of its intersections with the target
radical and its opposite. The factors exist on every test scheme. -/
theorem exists_factors_unipotent_opposite_of_centralizer_le [Smooth G.X.hom] [IsAffineHom G.X.hom]
    {C : CommGroupScheme S} (i : C.toGrp ⟶ G) (a b : (Gm S).toGrp ⟶ C.toGrp)
    (hZ : centralizer (b ≫ i) ≤ centralizer (a ≫ i))
    {T : Over S} {g : T ⟶ G.X} (hg : g ∈ (unipotent (a ≫ i)).carrier T) :
    ∃ u v : T ⟶ G.X, u ∈ (unipotent (a ≫ i) ⊓ unipotent (b ≫ i)).carrier T ∧
      v ∈ (unipotent (oppositeCocharacter (b ≫ i))).carrier T ∧ g = u * v := by
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let P := Affine.parabolicScheme (b ≫ i)
  let d := Affine.parabolicHom (b ≫ i)
  let V := Affine.unipotentScheme (oppositeCocharacter (b ≫ i))
  let j := Affine.unipotentHom (oppositeCocharacter (b ≫ i))
  let hp := Affine.isRepresentedBy_parabolicHom (b ≫ i)
  let hv := Affine.isRepresentedBy_unipotentHom (oppositeCocharacter (b ≫ i))
  let m := SubgroupFunctor.cellMultiplication j d
  let : IsOpenImmersion m.left := oppositeCellStatement k G (b ≫ i) V P j d hv hp
  let : Mono m := mono_oppositeCellMul (b ≫ i) hv hp
  have hV : (unipotent (oppositeCocharacter (b ≫ i))).IsNormalizedBy
      (SubgroupFunctor.range (a ≫ i)) := by
    simpa only [oppositeCocharacter, Category.assoc] using
      unipotent_isNormalizedBy_range_of_common_commutativeGroup i a
        (CommGroupScheme.groupHom (Gm.powerHom S (-1)) ≫ b)
  have hP := parabolic_isNormalizedBy_range_of_common_commutativeGroup i a b
  have hstab : IsCocharacterStable (a ≫ i) m :=
    isCocharacterStable_product _ j d (hv.2.symm ▸ hV) (hp.2.symm ▸ hP)
  obtain ⟨e, he, he0⟩ := ((unipotent (a ≫ i)).carrier T).inv_mem hg
  let z := lift (1 : Over.mk (𝟙 S) ⟶ V.X) (1 : Over.mk (𝟙 S) ⟶ P.X)
  have hz : z ≫ m = 1 := by
    change z ≫ ((fst V.X P.X ≫ j.hom.hom) * (snd V.X P.X ≫ d.hom.hom)) = 1
    have hfst : z ≫ fst V.X P.X = 1 := lift_fst _ _
    have hsnd : z ≫ snd V.X P.X = 1 := lift_snd _ _
    rw [MonObj.comp_mul, ← Category.assoc z, hfst, ← Category.assoc z, hsnd,
      MonObj.one_comp, MonObj.one_comp, one_mul]
  obtain ⟨e', he'⟩ := exists_lift_contraction_stableOpen (a ≫ i) m hstab z hz he he0
  have hprod := hasProductContraction_of_represented_lift (a ≫ i) _ _ hv hp he he0 e' he'
  have hinj (X : Over S) : Function.Injective
      (fun z : (unipotent (oppositeCocharacter (b ≫ i))).carrier X × (parabolic (b ≫ i)).carrier X =>
        (z.1 : X ⟶ G.X) * z.2) := by
    rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ ⟨⟨x', hx'⟩, ⟨y', hy'⟩⟩ heq
    obtain ⟨x₀, rfl⟩ := SubgroupFunctor.mem_range.mp (hv.2.symm ▸ hx)
    obtain ⟨y₀, rfl⟩ := SubgroupFunctor.mem_range.mp (hp.2.symm ▸ hy)
    obtain ⟨x₁, rfl⟩ := SubgroupFunctor.mem_range.mp (hv.2.symm ▸ hx')
    obtain ⟨y₁, rfl⟩ := SubgroupFunctor.mem_range.mp (hp.2.symm ▸ hy')
    have hxy : lift x₀ y₀ = lift x₁ y₁ := (cancel_mono m).mp (by
      simpa only [m, SubgroupFunctor.cellMultiplication, MonObj.comp_mul,
        lift_fst_assoc, lift_snd_assoc] using heq)
    have hx₀ : x₀ = x₁ := (lift_fst x₀ y₀).symm.trans
      ((congrArg (fun f : X ⟶ V.X ⊗ P.X => f ≫ fst V.X P.X) hxy).trans (lift_fst x₁ y₁))
    have hy₀ : y₀ = y₁ := (lift_snd x₀ y₀).symm.trans
      ((congrArg (fun f : X ⟶ V.X ⊗ P.X => f ≫ snd V.X P.X) hxy).trans (lift_snd x₁ y₁))
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · exact congrArg (· ≫ j.hom.hom) hx₀
    · exact congrArg (· ≫ d.hom.hom) hy₀
  obtain ⟨v, u, hv', hu, _, hu', hxy⟩ := hprod.exists_unipotent_factors _ _ _ hV hP hinj
  have huV := mem_unipotent_of_mem_unipotent_of_mem_parabolic (a ≫ i) (b ≫ i) hZ hu' hu
  refine ⟨u⁻¹, v⁻¹, ⟨((unipotent (a ≫ i)).carrier T).inv_mem hu',
    ((unipotent (b ≫ i)).carrier T).inv_mem huV⟩,
    ((unipotent (oppositeCocharacter (b ≫ i))).carrier T).inv_mem hv', ?_⟩
  simpa only [inv_inv, mul_inv_rev] using congrArg Inv.inv hxy

end Langlands.GroupScheme.Dynamic
