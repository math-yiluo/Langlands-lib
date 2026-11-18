import Langlands.GroupScheme.Torus.AffineCharacterAction
import Langlands.GroupScheme.Torus.CharacterActionNilpotentRigidity
import Langlands.GroupScheme.Torus.MultiplicativeTypeAffineInfinitesimalCentrality

/-! # Nilpotent centrality for multiplicative-type sources and arbitrary targets -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme

namespace NilpotentConjugation

open AutomorphicAction

variable {R : CommRingCat.{u}} {N : Type u} [AddCommGroup N]
  {H : GroupScheme (Spec R)} (u : (Diagonalizable.groupScheme R N).toGrp ⟶ H)

/-- Conjugation of a point of `H` by the image under `u` of a diagonalizable point. -/
abbrev conj {T : Over (Spec R)} (x : T ⟶ (Diagonalizable.groupScheme R N).X) (h : T ⟶ H.X) :
    T ⟶ H.X :=
  (conjugation u).act x h

theorem conj_eq {T : Over (Spec R)} (x : T ⟶ (Diagonalizable.groupScheme R N).X)
    (h : T ⟶ H.X) : conj u x h = (x ≫ u.hom.hom) * h * (x ≫ u.hom.hom)⁻¹ :=
  conjugation_act u x h

theorem conj_eq_self_iff {T : Over (Spec R)} (x : T ⟶ (Diagonalizable.groupScheme R N).X)
    (h : T ⟶ H.X) : conj u x h = h ↔ Commute (x ≫ u.hom.hom) h := by
  rw [conj_eq, mul_inv_eq_iff_eq_mul]
  rfl

/-- Over an algebra killed by `I`, the image of `u` commutes with every point of `H`. -/
theorem commute_of_quotient (I : Ideal R)
    (hc : IsCentral ((GroupScheme.baseChange (Spec.algebraMap R (R ⧸ I))).map u))
    (Y : CommAlgCat.{u} R) (hY : ∀ r : R, r ∈ I → algebraMap R Y r = 0)
    (x : (algSpec R).obj (op Y) ⟶ (Diagonalizable.groupScheme R N).X)
    (h : (algSpec R).obj (op Y) ⟶ H.X) :
    Commute (x ≫ u.hom.hom) h := by
  let b := Spec.algebraMap R (R ⧸ I)
  let t : Spec (CommRingCat.of Y) ⟶ Spec (CommRingCat.of (R ⧸ I)) :=
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.lift I (algebraMap R Y) hY))
  let T : Over (Spec (CommRingCat.of (R ⧸ I))) := Over.mk t
  let e : (Over.map b).obj T ≅ (algSpec R).obj (op Y) :=
    Over.isoMk (Iso.refl _) (by
      change 𝟙 _ ≫ Spec.map (CommRingCat.ofHom (algebraMap R Y)) = t ≫ b
      rw [Category.id_comp]
      change _ = Spec.map (CommRingCat.ofHom (Ideal.Quotient.lift I (algebraMap R Y) hY)) ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
      rw [← Spec.map_comp]
      rfl)
  let G := (Diagonalizable.groupScheme R N).toGrp
  let x' := (baseChangePointsEquiv b G T).symm (e.hom ≫ x)
  let y' := (baseChangePointsEquiv b H T).symm (e.hom ≫ h)
  have hxy : Commute (x' ≫ ((Over.pullback b).mapGrp.map u).hom.hom) y' :=
    commute_of_mem_center (hc T x') y'
  have he := congrArg (baseChangePointsEquiv b H T) hxy.eq
  apply (cancel_epi e.hom).mp
  simpa only [map_mul, baseChangePointsEquiv_comp, x', y',
    MulEquiv.apply_symm_apply, MonObj.comp_mul, Category.assoc] using he

/-- Over an affine test, conjugation by `u` does not move the underlying points, since it is
trivial on the reduction modulo the nilpotent ideal `I`. -/
theorem conj_left_apply (I : Ideal R) (hI : IsNilpotent I)
    (hc : IsCentral ((GroupScheme.baseChange (Spec.algebraMap R (R ⧸ I))).map u))
    {C : CommAlgCat.{u} R} (x : (algSpec R).obj (op C) ⟶ (Diagonalizable.groupScheme R N).X)
    (p : (algSpec R).obj (op C) ⟶ H.X) (z : ((algSpec R).obj (op C)).left) :
    (conj u x p).left z = p.left z := by
  let J := I.map (algebraMap R C)
  let Q : CommAlgCat.{u} R := CommAlgCat.of R (C ⧸ J)
  let q : C ⟶ Q := CommAlgCat.ofHom (Ideal.Quotient.mkₐ R J)
  let π := (algSpec R).map q.op
  have hQ : ∀ r : R, r ∈ I → algebraMap R Q r = 0 := fun r hr =>
    (Ideal.Quotient.eq_zero_iff_mem).mpr (Ideal.mem_map_of_mem (algebraMap R C) hr)
  have hπ : π ≫ conj u x p = π ≫ p := by
    rw [AutomorphicAction.naturality]
    exact (conj_eq_self_iff u _ _).mpr (commute_of_quotient u I hc Q hQ _ _)
  have hJ : J ≤ nilradical C := by
    obtain ⟨n, hn⟩ := hI
    intro c hc'
    refine ⟨n, ?_⟩
    have h1 : c ^ n ∈ J ^ n := Ideal.pow_mem_pow hc' n
    rw [← Ideal.map_pow, hn, Ideal.zero_eq_bot, Ideal.map_bot] at h1
    exact h1
  have hsurj : Function.Surjective π.left :=
    (PrimeSpectrum.comap_quotientMk_bijective_of_le_nilradical hJ).2
  obtain ⟨w, rfl⟩ := hsurj z
  have h := congrArg (fun f => f.left w) hπ
  simpa only [Over.comp_left, Scheme.Hom.comp_apply] using h

section Chart

variable {B : CommAlgCat.{u} R} (φ : (algSpec R).obj (op B) ⟶ H.X)

/-- The point of `H` obtained from a point of the chart `φ`. -/
def chartPoint {C : CommAlgCat.{u} R} (y : B ⟶ C) : (algSpec R).obj (op C) ⟶ H.X :=
  (algSpec R).map y.op ≫ φ

theorem chartPoint_comp {C D : CommAlgCat.{u} R} (y : B ⟶ C) (f : C ⟶ D) :
    chartPoint φ (y ≫ f) = (algSpec R).map f.op ≫ chartPoint φ y := by
  unfold chartPoint
  rw [op_comp, Functor.map_comp, Category.assoc]

variable [IsOpenImmersion φ.left]

theorem chartPoint_injective {C : CommAlgCat.{u} R} :
    Function.Injective (chartPoint φ (C := C)) := by
  intro y y' h
  have h' : (algSpec R).map y.op = (algSpec R).map y'.op := by
    apply Over.OverMorphism.ext
    exact (cancel_mono φ.left).mp (congrArg CommaMorphism.left h)
  exact Quiver.Hom.op_inj (algSpec.fullyFaithful.map_injective h')

theorem exists_chartPoint {C : CommAlgCat.{u} R} (p : (algSpec R).obj (op C) ⟶ H.X)
    (hp : Set.range p.left ⊆ Set.range φ.left) : ∃ y : B ⟶ C, chartPoint φ y = p := by
  let g := IsOpenImmersion.lift φ.left p.left hp
  have hg : g ≫ φ.left = p.left := IsOpenImmersion.lift_fac _ _ _
  let g' : (algSpec R).obj (op C) ⟶ (algSpec R).obj (op B) := Over.homMk g (by
    rw [← Over.w φ, ← Category.assoc, hg, Over.w p])
  refine ⟨(algSpec.fullyFaithful.preimage g').unop, ?_⟩
  unfold chartPoint
  rw [Quiver.Hom.op_unop, algSpec.fullyFaithful.map_preimage]
  apply Over.OverMorphism.ext
  simp only [Over.comp_left, g', Over.homMk_left, hg]

variable (I : Ideal R) (hI : IsNilpotent I)
  (hc : IsCentral ((GroupScheme.baseChange (Spec.algebraMap R (R ⧸ I))).map u))
include hI hc

omit [IsOpenImmersion φ.left] in
theorem range_conj_subset {C : CommAlgCat.{u} R}
    (x : (algSpec R).obj (op C) ⟶ (Diagonalizable.groupScheme R N).X) (y : B ⟶ C) :
    Set.range (conj u x (chartPoint φ y)).left ⊆ Set.range φ.left := by
  rintro _ ⟨z, rfl⟩
  rw [conj_left_apply u I hI hc]
  exact ⟨((algSpec R).map y.op).left z, rfl⟩

omit hI hc in
/-- The conjugation action in the coordinates of the chart `φ`. -/
def chartAct (hI : IsNilpotent I)
    (hc : IsCentral ((GroupScheme.baseChange (Spec.algebraMap R (R ⧸ I))).map u))
    {C : CommAlgCat.{u} R} (t : Multiplicative N →* Cˣ) (y : B ⟶ C) : B ⟶ C :=
  Classical.choose (exists_chartPoint φ _
    (range_conj_subset u φ I hI hc (CharacterAction.characterPoint t) y))

theorem chartPoint_chartAct {C : CommAlgCat.{u} R} (t : Multiplicative N →* Cˣ) (y : B ⟶ C) :
    chartPoint φ (chartAct u φ I hI hc t y) =
      conj u (CharacterAction.characterPoint t) (chartPoint φ y) :=
  Classical.choose_spec (exists_chartPoint φ _
    (range_conj_subset u φ I hI hc (CharacterAction.characterPoint t) y))

/-- Conjugation by `u` as a character action on the coordinate algebra of the chart. -/
def chartAction : CharacterAction.Action (M := N) B where
  act t y := chartAct u φ I hI hc t y
  one {C} y := by
    apply chartPoint_injective φ
    rw [chartPoint_chartAct, CharacterAction.characterPoint_one]
    exact (conjugation u).act_one_left _
  mul {C} t s y := by
    apply chartPoint_injective φ
    rw [chartPoint_chartAct, chartPoint_chartAct, chartPoint_chartAct,
      CharacterAction.characterPoint_mul]
    exact (conjugation u).act_mul_left _ _ _
  naturality {C D} f t y := by
    apply chartPoint_injective φ
    rw [chartPoint_chartAct, chartPoint_comp, chartPoint_comp, chartPoint_chartAct,
      CharacterAction.characterPoint_mapCharacter, AutomorphicAction.naturality]

/-- Conjugation by `u` fixes every point of an affine open chart of `H`. -/
theorem conj_chartPoint {C : CommAlgCat.{u} R} (t : Multiplicative N →* Cˣ) (y : B ⟶ C) :
    conj u (CharacterAction.characterPoint t) (chartPoint φ y) = chartPoint φ y := by
  have hfix : ∀ (C : CommAlgCat.{u} R), (∀ r ∈ I, algebraMap R C r = 0) →
      ∀ (t : Multiplicative N →* Cˣ) (x : B ⟶ C), (chartAction u φ I hI hc).act t x = x := by
    intro C hC t x
    apply chartPoint_injective φ
    change chartPoint φ (chartAct u φ I hI hc t x) = _
    rw [chartPoint_chartAct]
    exact (conj_eq_self_iff u _ _).mpr (commute_of_quotient u I hc C hC _ _)
  have h := CharacterAction.act_eq_of_nilpotent_quotient (chartAction u φ I hI hc) I hI hfix t y
  change chartAct u φ I hI hc t y = y at h
  rw [← chartPoint_chartAct u φ I hI hc, h]

end Chart

/-- Two morphisms out of `T` agree if, near every point of `T`, they agree on all affine points
of `T` over `Spec R` whose image lies in a given open neighbourhood. -/
theorem hom_ext_of_affine {T Y : Over (Spec R)} (f g : T ⟶ Y)
    (hfg : ∀ z : T.left, ∃ U : T.left.Opens, z ∈ U ∧ ∀ (C : CommAlgCat.{u} R)
      (w : (algSpec R).obj (op C) ⟶ T), Set.range w.left ⊆ U → w ≫ f = w ≫ g) :
    f = g := by
  apply Over.OverMorphism.ext
  apply Scheme.hom_ext_of_forall
  intro z
  obtain ⟨U, hzU, hU⟩ := hfg z
  obtain ⟨W, hW, hzW, hWU⟩ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp T.left.isBasis_affineOpens hzU
  have hW' : IsAffineOpen W := hW
  refine ⟨W, hzW, ?_⟩
  let A := Γ(T.left, W)
  let _ : Algebra R A := (Spec.preimage (hW'.fromSpec ≫ T.hom)).hom.toAlgebra
  have hb : Spec.algebraMap R A = hW'.fromSpec ≫ T.hom := Spec.map_preimage _
  let w : (algSpec R).obj (op (CommAlgCat.of R A)) ⟶ T := Over.homMk hW'.fromSpec hb.symm
  have hw := hU (CommAlgCat.of R A) w (by
    change Set.range hW'.fromSpec ⊆ U
    rw [hW'.range_fromSpec]
    exact hWU)
  have hwl : hW'.fromSpec ≫ f.left = hW'.fromSpec ≫ g.left :=
    congrArg CommaMorphism.left hw
  have hι : Scheme.Opens.ι W = hW'.isoSpec.hom ≫ hW'.fromSpec := by
    rw [← hW'.isoSpec_inv_ι, Iso.hom_inv_id_assoc]
  rw [hι, Category.assoc, Category.assoc, hwl]

/-- Conjugation by `u` fixes every affine point of `H` landing in an affine open. -/
theorem conj_eq_of_range_subset (I : Ideal R) (hI : IsNilpotent I)
    (hc : IsCentral ((GroupScheme.baseChange (Spec.algebraMap R (R ⧸ I))).map u))
    {C : CommAlgCat.{u} R} (x : (algSpec R).obj (op C) ⟶ (Diagonalizable.groupScheme R N).X)
    (p : (algSpec R).obj (op C) ⟶ H.X) (V : H.X.left.Opens) (hV : IsAffineOpen V)
    (hp : Set.range p.left ⊆ V) : conj u x p = p := by
  let A := Γ(H.X.left, V)
  let _ : Algebra R A := (Spec.preimage (hV.fromSpec ≫ H.X.hom)).hom.toAlgebra
  have hb : Spec.algebraMap R A = hV.fromSpec ≫ H.X.hom := Spec.map_preimage _
  let φ : (algSpec R).obj (op (CommAlgCat.of R A)) ⟶ H.X := Over.homMk hV.fromSpec hb.symm
  have : IsOpenImmersion φ.left := by
    change IsOpenImmersion hV.fromSpec
    infer_instance
  obtain ⟨y, rfl⟩ := exists_chartPoint φ p (by
    change Set.range p.left ⊆ Set.range hV.fromSpec
    rw [hV.range_fromSpec]
    exact hp)
  obtain ⟨t, rfl⟩ : ∃ t : Multiplicative N →* Cˣ, CharacterAction.characterPoint t = x :=
    ⟨Corepresented.affinePointsEquiv (Diagonalizable.functor R N)
      (Diagonalizable.grpCorepresentation R N) C x, MulEquiv.symm_apply_apply _ x⟩
  exact conj_chartPoint u φ I hI hc t y

/-- **Nilpotent centrality for the standard diagonalizable source and an arbitrary target.** -/
theorem isCentral (I : Ideal R) (hI : IsNilpotent I)
    (hc : IsCentral ((GroupScheme.baseChange (Spec.algebraMap R (R ⧸ I))).map u)) :
    IsCentral u := by
  intro T x
  apply mem_center.mpr
  intro T' a h
  rw [← Category.assoc]
  apply (conj_eq_self_iff u _ _).mp
  apply hom_ext_of_affine
  intro z
  obtain ⟨V, hV, hzV, -⟩ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp H.X.left.isBasis_affineOpens
    (show h.left z ∈ (⊤ : H.X.left.Opens) from trivial)
  refine ⟨h.left ⁻¹ᵁ V, hzV, fun C w hw => ?_⟩
  rw [AutomorphicAction.naturality]
  apply conj_eq_of_range_subset u I hI hc _ _ V hV
  rintro _ ⟨y, rfl⟩
  exact hw ⟨y, rfl⟩

/-- Nilpotent centrality for a diagonalizable source over an affine base and an arbitrary
target. -/
theorem isCentral_of_isDiagonalizable {G H : GroupScheme (Spec R)}
    (hG : RelativeMultiplicativeType.IsDiagonalizable G) (i : G ⟶ H)
    (I : Ideal R) (hI : IsNilpotent I)
    (hc : IsCentral ((GroupScheme.baseChange (Spec.algebraMap R (R ⧸ I))).map i)) :
    IsCentral i := by
  obtain ⟨L, _, _, ⟨e⟩⟩ := hG
  let d : (Diagonalizable.groupScheme R L).toGrp ≅ G :=
    (Diagonalizable.baseChangeIso (Gm.toSpecZ (Spec R)) L).symm ≪≫ e.symm
  have hd : IsCentral
      ((GroupScheme.baseChange (Spec.algebraMap R (R ⧸ I))).map (d.hom ≫ i)) := by
    rw [Functor.map_comp]
    exact hc.comp _
  have h := (isCentral (d.hom ≫ i) I hI hd).comp d.inv
  simpa only [Iso.inv_hom_id_assoc] using h

open MultiplicativeTypeAffineInfinitesimalCentrality in
/-- Centrality lifts on an affine algebra chart over which the source is diagonalizable. -/
theorem isCentral_baseChange_of_isDiagonalizable {B : CommRingCat.{u}} [Algebra R B]
    {G H : GroupScheme (Spec R)} (i : G ⟶ H)
    (hG : RelativeMultiplicativeType.IsDiagonalizable
      ((GroupScheme.baseChange (Spec.algebraMap R B)).obj G))
    (I : Ideal R) (hI : IsNilpotent I)
    (hc : IsCentral ((GroupScheme.baseChange (Spec.algebraMap R (R ⧸ I))).map i)) :
    IsCentral ((GroupScheme.baseChange (Spec.algebraMap R B)).map i) :=
  isCentral_of_isDiagonalizable hG _ (I.map (algebraMap R B)) (isNilpotent_map I hI)
    (isCentral_quotient_baseChange i I hc)

/-- The affine chart need not come with a specified algebra structure. -/
theorem isCentral_affineChart_of_isDiagonalizable {B : CommRingCat.{u}}
    {G H : GroupScheme (Spec R)} (b : Spec B ⟶ Spec R) (i : G ⟶ H)
    (hG : RelativeMultiplicativeType.IsDiagonalizable ((GroupScheme.baseChange b).obj G))
    (I : Ideal R) (hI : IsNilpotent I)
    (hc : IsCentral ((GroupScheme.baseChange (Spec.algebraMap R (R ⧸ I))).map i)) :
    IsCentral ((GroupScheme.baseChange b).map i) := by
  let : Algebra R B := (Spec.preimage b).hom.toAlgebra
  have hb : Spec.algebraMap R B = b := Spec.map_preimage b
  rw [← hb] at hG ⊢
  exact isCentral_baseChange_of_isDiagonalizable i hG I hI hc

open MultiplicativeTypeAffineInfinitesimalCentrality in
/-- **Nilpotent centrality over an affine base** for a multiplicative-type source and an
arbitrary target. -/
theorem isCentral_of_isMultiplicativeType {G H : GroupScheme (Spec R)}
    (hG : RelativeMultiplicativeType.IsMultiplicativeType G) (i : G ⟶ H)
    (I : Ideal R) (hI : IsNilpotent I)
    (hc : IsCentral ((GroupScheme.baseChange (Spec.algebraMap R (R ⧸ I))).map i)) :
    IsCentral i := by
  obtain ⟨𝒰, h𝒰⟩ := hG
  apply IsCentral.of_flatCover (𝒰.changeProp (Q := @Flat) fun j => (𝒰.map_prop j).1)
  intro j
  let 𝒱 := (𝒰.X j).affineOpenCover
  apply IsCentral.of_flatCover (𝒱.openCover.changeProp (Q := @Flat) fun _ => inferInstance)
  intro k
  apply (isCentral_baseChange_comp_iff (𝒰.f j) (𝒱.f k) i).mp
  apply isCentral_affineChart_of_isDiagonalizable (𝒱.f k ≫ 𝒰.f j) i _ I hI hc
  exact RelativeMultiplicativeType.IsDiagonalizable.of_iso
    (Descent.pullbackComparison (𝒰.f j) (𝒱.f k) (𝒱.f k ≫ 𝒰.f j) rfl G).symm
    ((h𝒰 j).baseChange (𝒱.f k))

end NilpotentConjugation

end Langlands.GroupScheme
