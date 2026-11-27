import Langlands.AbelianScheme.Basic
import Langlands.AlgebraicGeometry.AffineNilpotentThickening
import Langlands.RingTheory.ArtinianCharZeroCoefficientField
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Langlands.AlgebraicGeometry.TwistedOpenGluing

/-! # Constant charts of an abelian scheme across an Artinian extension -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AbelianScheme.ArtinianConstantCharts

/-- A surjection `φ : R' → R` of local rings with a coefficient field `σ` of `R'` and the
induced residue map `ψ : R → k` of `R`, where `k` is the residue field of `R'`. -/
structure Setting (R' R : Type u) [CommRing R'] [CommRing R] [IsLocalRing R'] where
  φ : R' →+* R
  surj : Function.Surjective φ
  σ : ResidueField R' →+* R'
  hσ : (residue R').comp σ = RingHom.id _
  ψ : R →+* ResidueField R'
  hψ : ψ.comp φ = residue R'

variable {R' R : Type u} [CommRing R'] [CommRing R] [IsLocalRing R']

theorem Setting.exists [IsArtinianRing R'] [Algebra ℚ R'] (φ : R' →+* R)
    (hφ : Function.Surjective φ) (hker : RingHom.ker φ ≤ maximalIdeal R') :
    ∃ S : Setting R' R, S.φ = φ := by
  obtain ⟨σ, hσ⟩ := RingTheory.exists_coefficientField R'
  let g : { g : R' →+* ResidueField R' // RingHom.ker φ ≤ RingHom.ker g } :=
    ⟨residue R', by rwa [ker_residue]⟩
  let ψ : R →+* ResidueField R' := (RingHom.liftOfSurjective (C := ResidueField R') φ hφ) g
  have hψ : ψ.comp φ = residue R' := by
    ext x
    exact RingHom.liftOfSurjective_comp_apply φ hφ g x
  exact ⟨⟨φ, hφ, σ, hσ, ψ, hψ⟩, rfl⟩

namespace Setting

variable (S : Setting R' R)

theorem ψ_surjective : Function.Surjective S.ψ := by
  intro x
  obtain ⟨y, rfl⟩ := residue_surjective (R := R') x
  exact ⟨S.φ y, by rw [← RingHom.comp_apply, S.hψ]⟩

theorem isNilpotent_ker_ψ [IsArtinianRing R'] : IsNilpotent (RingHom.ker S.ψ) := by
  obtain ⟨n, hn⟩ := RingTheory.isNilpotent_ker_residue R'
  refine ⟨n, eq_bot_iff.mpr fun x hx ↦ ?_⟩
  have hle : RingHom.ker S.ψ ≤ (RingHom.ker (residue R')).map S.φ := by
    intro y hy
    obtain ⟨z, rfl⟩ := S.surj y
    refine Ideal.mem_map_of_mem _ ?_
    rw [RingHom.mem_ker, ← S.hψ, RingHom.comp_apply]
    exact hy
  have : x ∈ ((RingHom.ker (residue R')) ^ n).map S.φ := by
    rw [Ideal.map_pow]
    exact Ideal.pow_right_mono hle n hx
  rwa [hn, Ideal.zero_eq_bot, Ideal.map_bot] at this

/-- The closed point of `Spec R`, through the residue field of `R'`. -/
abbrev c : Spec (CommRingCat.of (ResidueField R')) ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom S.ψ)

/-- The closed immersion `Spec R ⟶ Spec R'` on spectra induced by `φ`. -/
abbrev t : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of R') := Spec.map (CommRingCat.ofHom S.φ)

/-- The structure map of `Spec R'` over the coefficient field. -/
abbrev sσ : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of (ResidueField R')) :=
  Spec.map (CommRingCat.ofHom S.σ)

theorem c_t_sσ : S.c ≫ S.t ≫ S.sσ = 𝟙 _ := by
  rw [← Spec.map_comp, ← Spec.map_comp, ← Spec.map_id]
  congr 1
  ext x
  change S.ψ (S.φ (S.σ x)) = x
  rw [← RingHom.comp_apply S.ψ S.φ, S.hψ, ← RingHom.comp_apply, S.hσ, RingHom.id_apply]

variable (B : AbelianScheme (Spec (CommRingCat.of R)))

/-- The special fibre of `B`, an abelian variety over the residue field of `R'`. -/
abbrev A₀ : AbelianScheme (Spec (CommRingCat.of (ResidueField R'))) :=
  (AbelianScheme.baseChange S.c).obj B

/-- The inclusion of the special fibre. -/
abbrev jB : (S.A₀ B).X.left ⟶ B.X.left := pullback.fst B.X.hom S.c

/-- The constant abelian scheme over `R'` with special fibre `A₀`. -/
abbrev C : AbelianScheme (Spec (CommRingCat.of R')) :=
  (AbelianScheme.baseChange S.sσ).obj (S.A₀ B)

/-- The reduction of the constant abelian scheme to `R`. -/
abbrev CS : Scheme.{u} := pullback (S.C B).X.hom S.t

/-- The projection of the reduced constant scheme to the special fibre. -/
abbrev ρ : S.CS B ⟶ (S.A₀ B).X.left :=
  pullback.fst (S.C B).X.hom S.t ≫ pullback.fst (S.A₀ B).X.hom S.sσ

theorem isPullback_ρ :
    IsPullback (S.ρ B) (pullback.snd (S.C B).X.hom S.t) (S.A₀ B).X.hom (S.t ≫ S.sσ) :=
  (IsPullback.of_hasPullback (S.C B).X.hom S.t).paste_horiz
    (IsPullback.of_hasPullback (S.A₀ B).X.hom S.sσ)

/-- The special fibre as the constant section of the reduced constant scheme. -/
def τ : (S.A₀ B).X.left ⟶ S.CS B :=
  (S.isPullback_ρ B).lift (𝟙 _) ((S.A₀ B).X.hom ≫ S.c) (by
    rw [Category.id_comp, Category.assoc, S.c_t_sσ, Category.comp_id])

@[reassoc (attr := simp)]
theorem τ_ρ : S.τ B ≫ S.ρ B = 𝟙 _ := (S.isPullback_ρ B).lift_fst _ _ _

@[reassoc (attr := simp)]
theorem τ_snd : S.τ B ≫ pullback.snd (S.C B).X.hom S.t = (S.A₀ B).X.hom ≫ S.c :=
  (S.isPullback_ρ B).lift_snd _ _ _

theorem isPullback_τ :
    IsPullback (S.τ B) (S.A₀ B).X.hom (pullback.snd (S.C B).X.hom S.t) S.c := by
  refine IsPullback.of_right ?_ (S.τ_snd B) (S.isPullback_ρ B)
  rw [τ_ρ, S.c_t_sσ]
  exact IsPullback.of_horiz_isIso ⟨by simp⟩

section Chart

variable (U : B.X.left.Opens)

/-- The special fibre of an open of `B`, as an open of `A₀`. -/
abbrev W : (S.A₀ B).X.left.Opens := S.jB B ⁻¹ᵁ U

/-- The corresponding open of the reduced constant scheme. -/
abbrev VT : (S.CS B).Opens := S.ρ B ⁻¹ᵁ S.W B U

/-- The inclusion of the special fibre of `U` into `U`. -/
abbrev a : (S.W B U).toScheme ⟶ U.toScheme := S.jB B ∣_ U

theorem W_le_τ_preimage : S.W B U ≤ S.τ B ⁻¹ᵁ S.VT B U := by
  intro x hx
  change (S.ρ B) ((S.τ B) x) ∈ S.W B U
  rw [← Scheme.Hom.comp_apply, τ_ρ]
  exact hx

/-- The special fibre of `U` as the constant section of `VT`. -/
abbrev a' : (S.W B U).toScheme ⟶ (S.VT B U).toScheme :=
  (S.τ B).resLE (S.VT B U) (S.W B U) (S.W_le_τ_preimage B U)

/-- The structure map of the special fibre of `U`. -/
abbrev w : (S.W B U).toScheme ⟶ Spec (CommRingCat.of (ResidueField R')) :=
  (S.W B U).ι ≫ (S.A₀ B).X.hom

theorem isPullback_a : IsPullback (S.a B U) (S.w B U) (U.ι ≫ B.X.hom) S.c :=
  (isPullback_morphismRestrict (S.jB B) U).paste_vert (IsPullback.of_hasPullback B.X.hom S.c)

@[reassoc]
theorem a'_ι : S.a' B U ≫ (S.VT B U).ι = (S.W B U).ι ≫ S.τ B := Scheme.Hom.resLE_comp_ι _ _

theorem a'_ρ : S.a' B U ≫ S.ρ B ∣_ S.W B U = 𝟙 _ := by
  rw [← cancel_mono (S.W B U).ι, Category.assoc, morphismRestrict_ι, a'_ι_assoc, τ_ρ,
    Category.comp_id, Category.id_comp]

theorem isPullback_a' :
    IsPullback (S.a' B U) (S.w B U) ((S.VT B U).ι ≫ pullback.snd (S.C B).X.hom S.t) S.c := by
  have hr : IsPullback (S.ρ B ∣_ S.W B U) ((S.VT B U).ι ≫ pullback.snd (S.C B).X.hom S.t)
      (S.w B U) (S.t ≫ S.sσ) :=
    (isPullback_morphismRestrict (S.ρ B) (S.W B U)).paste_vert (S.isPullback_ρ B)
  refine IsPullback.of_right ?_ ?_ hr
  · rw [a'_ρ, S.c_t_sσ]
    exact IsPullback.of_horiz_isIso ⟨by simp⟩
  · rw [a'_ι_assoc, τ_snd, Category.assoc]

instance isAffineHom_jB : IsAffineHom (S.jB B) :=
  MorphismProperty.pullback_fst (P := @IsAffineHom) _ _ inferInstance

instance isAffineHom_ρ : IsAffineHom (S.ρ B) := by
  have : IsAffineHom (pullback.fst (S.C B).X.hom S.t) :=
    MorphismProperty.pullback_fst (P := @IsAffineHom) _ _ inferInstance
  have : IsAffineHom (pullback.fst (S.A₀ B).X.hom S.sσ) :=
    MorphismProperty.pullback_fst (P := @IsAffineHom) _ _ inferInstance
  exact inferInstanceAs (IsAffineHom (_ ≫ _))

theorem isAffineOpen_W (hU : IsAffineOpen U) : IsAffineOpen (S.W B U) := hU.preimage _

theorem isAffineOpen_VT (hU : IsAffineOpen U) : IsAffineOpen (S.VT B U) :=
  (S.isAffineOpen_W B U hU).preimage _

/-- The constant chart: the reduced constant open is isomorphic to `U`, compatibly with the
special fibre and the structure maps. -/
theorem exists_chartIso [IsArtinianRing R'] (hU : IsAffineOpen U) :
    ∃ h : (S.VT B U).toScheme ≅ U.toScheme,
      h.hom ≫ U.ι ≫ B.X.hom = (S.VT B U).ι ≫ pullback.snd (S.C B).X.hom S.t ∧
        S.a' B U ≫ h.hom = S.a B U := by
  let := S.ψ.toAlgebra
  have : IsAffine U.toScheme := hU
  have : IsAffine (S.VT B U).toScheme := S.isAffineOpen_VT B U hU
  exact Langlands.AlgebraicGeometry.AffineNilpotentThickening.exists_iso_of_fibre (R₀ := ResidueField R') S.ψ_surjective
    S.isNilpotent_ker_ψ (U.ι ≫ B.X.hom) ((S.VT B U).ι ≫ pullback.snd (S.C B).X.hom S.t)
    (S.a B U) (S.a' B U) (S.w B U) (S.isPullback_a B U) (S.isPullback_a' B U)

end Chart

section Points

variable [IsArtinianRing R]

omit [IsLocalRing R'] in
/-- A local Artinian ring has a single prime ideal. -/
theorem primeSpectrum_subsingleton [IsLocalRing R] : Subsingleton (PrimeSpectrum R) := by
  constructor
  intro p q
  ext1
  rw [IsLocalRing.eq_maximalIdeal ((IsArtinianRing.isPrime_iff_isMaximal _).mp p.2),
    IsLocalRing.eq_maximalIdeal ((IsArtinianRing.isPrime_iff_isMaximal _).mp q.2)]

theorem c_surjective [IsLocalRing R] : Surjective S.c := by
  have := primeSpectrum_subsingleton (R := R)
  constructor
  intro y
  exact ⟨IsLocalRing.closedPoint (ResidueField R'),
    @Subsingleton.elim (PrimeSpectrum R) this _ _⟩

instance τ_surjective [IsLocalRing R] : Surjective (S.τ B) := by
  have := S.c_surjective
  exact MorphismProperty.of_isPullback (P := @Surjective) (S.isPullback_τ B).flip inferInstance

theorem τ_ρ_apply [IsLocalRing R] (x : S.CS B) : S.τ B (S.ρ B x) = x := by
  obtain ⟨w, rfl⟩ := (S.τ B).surjective x
  rw [← Scheme.Hom.comp_apply (S.τ B) (S.ρ B), τ_ρ]
  rfl

theorem ρ_injective [IsLocalRing R] : Function.Injective (S.ρ B) := fun x y h ↦ by
  rw [← S.τ_ρ_apply B x, ← S.τ_ρ_apply B y, h]

/-- A chart of `U` compatible with the special fibre agrees with `jB ∘ ρ` on points. -/
theorem chart_apply [IsLocalRing R] {U : B.X.left.Opens} (κ : (S.VT B U).toScheme ⟶ B.X.left)
    (hκ : S.a' B U ≫ κ = (S.W B U).ι ≫ S.jB B) (x : (S.VT B U).toScheme) :
    κ x = S.jB B (S.ρ B ((S.VT B U).ι x)) := by
  have hx : S.ρ B ((S.VT B U).ι x) ∈ S.W B U := x.2
  let w : (S.W B U).toScheme := ⟨S.ρ B ((S.VT B U).ι x), hx⟩
  have hw : S.a' B U w = x := by
    apply (S.VT B U).ι.isOpenEmbedding.injective
    rw [← Scheme.Hom.comp_apply, a'_ι, Scheme.Hom.comp_apply]
    exact S.τ_ρ_apply B _
  conv_lhs => rw [← hw]
  rw [← Scheme.Hom.comp_apply, hκ, Scheme.Hom.comp_apply]
  rfl

end Points

/-- A finite family of compatible constant charts covering `B`. -/
structure Charts where
  J : Type u
  [fintype : Fintype J]
  U : J → B.X.left.Opens
  affine : ∀ i, IsAffineOpen (U i)
  cover : ⨆ i, U i = ⊤
  κ : ∀ i, (S.VT B (U i)).toScheme ⟶ B.X.left
  [isOpenImmersion : ∀ i, IsOpenImmersion (κ i)]
  opensRange_κ : ∀ i, (κ i).opensRange = U i
  κ_base : ∀ i, κ i ≫ B.X.hom = (S.VT B (U i)).ι ≫ pullback.snd (S.C B).X.hom S.t
  κ_fibre : ∀ i, S.a' B (U i) ≫ κ i = (S.W B (U i)).ι ≫ S.jB B

attribute [instance] Charts.fintype Charts.isOpenImmersion

/-- A quasi-compact scheme is covered by finitely many affine opens. -/
theorem exists_finite_affine_cover (X : Scheme.{u}) [CompactSpace X] :
    ∃ s : Finset X.affineOpens, ⨆ U : s, (U.1 : X.Opens) = ⊤ := by
  classical
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun U : X.affineOpens ↦ ((U : X.Opens) : Set X)) (fun U ↦ (U : X.Opens).isOpen)
    (fun x _ ↦ by
      obtain ⟨U, hU, hx, -⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := ⊤) trivial
      exact Set.mem_iUnion.mpr ⟨⟨U, hU⟩, hx⟩)
  refine ⟨s, eq_top_iff.mpr fun x _ ↦ ?_⟩
  obtain ⟨U, hU, hx⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ x))
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨U, hU⟩, hx⟩

theorem Charts.exists [IsArtinianRing R'] : Nonempty (S.Charts B) := by
  have : CompactSpace B.X.left := QuasiCompact.compactSpace_of_compactSpace B.X.hom
  obtain ⟨s, hs⟩ := exists_finite_affine_cover B.X.left
  have hchart (U : s) := S.exists_chartIso B U.1.1 U.1.2
  choose h hb hf using hchart
  exact ⟨{
    J := ULift.{u} s
    U := fun i ↦ i.down.1.1
    affine := fun i ↦ i.down.1.2
    cover := by
      rw [← hs]
      exact le_antisymm (iSup_le fun i ↦ le_iSup (fun U : s ↦ (U.1 : B.X.left.Opens)) i.down)
        (iSup_le fun U ↦ le_iSup (fun i : ULift.{u} s ↦ (i.down.1 : B.X.left.Opens)) ⟨U⟩)
    κ := fun i ↦ (h i.down).hom ≫ i.down.1.1.ι
    opensRange_κ := fun i ↦ by
      rw [Scheme.Hom.opensRange_comp_of_isIso, Scheme.Opens.opensRange_ι]
    κ_base := fun i ↦ by rw [Category.assoc, hb]
    κ_fibre := fun i ↦ by
      rw [← Category.assoc, hf, morphismRestrict_ι] }⟩

namespace Charts

open Langlands.AlgebraicGeometry.TwistedOpenGluing

variable {S B} (K : S.Charts B) [IsArtinianRing R] [IsLocalRing R]

theorem κ_apply (i : K.J) (x : (S.VT B (K.U i)).toScheme) :
    K.κ i x = S.jB B (S.ρ B ((S.VT B (K.U i)).ι x)) :=
  S.chart_apply B (K.κ i) (K.κ_fibre i) x

instance : IsClosedImmersion S.c :=
  IsClosedImmersion.spec_of_surjective _ S.ψ_surjective

omit [IsArtinianRing R] [IsLocalRing R] in
theorem jB_injective : Function.Injective (S.jB B) := (S.jB B).isClosedEmbedding.injective

theorem range_homOfLE_κ (i j : K.J) :
    Set.range ((S.CS B).homOfLE (inf_le_right : S.VT B (K.U i) ⊓ S.VT B (K.U j) ≤ _) ≫ K.κ j) ⊆
      Set.range (K.κ i) := by
  rintro _ ⟨y, rfl⟩
  have hr : Set.range (K.κ i) = (K.U i : Set B.X.left) :=
    congrArg (fun U : B.X.left.Opens ↦ (U : Set B.X.left)) (K.opensRange_κ i)
  rw [hr, Scheme.Hom.comp_apply, K.κ_apply,
    ← Scheme.Hom.comp_apply ((S.CS B).homOfLE _) (S.VT B (K.U j)).ι, Scheme.homOfLE_ι]
  exact y.2.1

/-- The transition from chart `j` to chart `i` on their overlap. -/
def lift (i j : K.J) :
    (S.VT B (K.U i) ⊓ S.VT B (K.U j)).toScheme ⟶ (S.VT B (K.U i)).toScheme :=
  IsOpenImmersion.lift (K.κ i) ((S.CS B).homOfLE inf_le_right ≫ K.κ j) (K.range_homOfLE_κ i j)

@[reassoc (attr := simp)]
theorem lift_κ (i j : K.J) :
    K.lift i j ≫ K.κ i = (S.CS B).homOfLE inf_le_right ≫ K.κ j :=
  IsOpenImmersion.lift_fac _ _ _

/-- The transition maps of the charts, as morphisms into the reduced constant scheme. -/
def θS (i j : K.J) : (S.VT B (K.U i) ⊓ S.VT B (K.U j)).toScheme ⟶ S.CS B :=
  K.lift i j ≫ (S.VT B (K.U i)).ι

theorem θS_pointwise (i j : K.J) : IsPointwiseInclusion (K.θS i j) := by
  intro y
  apply S.ρ_injective B
  apply jB_injective
  have h₁ : K.θS i j y = (S.VT B (K.U i)).ι (K.lift i j y) := Scheme.Hom.comp_apply _ _ _
  have h₂ : K.κ i (K.lift i j y) = K.κ j ((S.CS B).homOfLE inf_le_right y) := by
    rw [← Scheme.Hom.comp_apply, lift_κ, Scheme.Hom.comp_apply]
  have h₃ : (S.VT B (K.U j)).ι ((S.CS B).homOfLE inf_le_right y) =
      (S.VT B (K.U i) ⊓ S.VT B (K.U j)).ι y := by
    rw [← Scheme.Hom.comp_apply, Scheme.homOfLE_ι]
  rw [h₁, ← K.κ_apply, h₂, K.κ_apply, h₃]

theorem θS_self (i : K.J) : K.θS i i = (S.VT B (K.U i) ⊓ S.VT B (K.U i)).ι := by
  have : K.lift i i = (S.CS B).homOfLE inf_le_left :=
    (IsOpenImmersion.lift_uniq _ _ _ ((S.CS B).homOfLE inf_le_left) rfl).symm
  unfold θS
  rw [this, Scheme.homOfLE_ι]

theorem θS_cocycle (i j k : K.J) :
    restrictTo (K.θS j k) (K.θS_pointwise j k)
        (W := S.VT B (K.U i) ⊓ S.VT B (K.U j) ⊓ S.VT B (K.U k))
        (le_inf (inf_le_left.trans inf_le_right) inf_le_right) inf_le_left ≫ K.θS i j =
      (S.CS B).homOfLE (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
          S.VT B (K.U i) ⊓ S.VT B (K.U j) ⊓ S.VT B (K.U k) ≤
            S.VT B (K.U i) ⊓ S.VT B (K.U k)) ≫ K.θS i k := by
  have h₁ : restrictTo (K.θS j k) (K.θS_pointwise j k)
        (W := S.VT B (K.U i) ⊓ S.VT B (K.U j) ⊓ S.VT B (K.U k))
        (le_inf (inf_le_left.trans inf_le_right) inf_le_right) inf_le_left ≫
          (S.CS B).homOfLE (inf_le_right : S.VT B (K.U i) ⊓ S.VT B (K.U j) ≤ _) =
      (S.CS B).homOfLE (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
          S.VT B (K.U i) ⊓ S.VT B (K.U j) ⊓ S.VT B (K.U k) ≤
            S.VT B (K.U j) ⊓ S.VT B (K.U k)) ≫ K.lift j k := by
    rw [← cancel_mono (S.VT B (K.U j)).ι, Category.assoc, Scheme.homOfLE_ι, restrictTo_ι,
      Category.assoc]
    rfl
  have h₂ : restrictTo (K.θS j k) (K.θS_pointwise j k)
        (W := S.VT B (K.U i) ⊓ S.VT B (K.U j) ⊓ S.VT B (K.U k))
        (le_inf (inf_le_left.trans inf_le_right) inf_le_right) inf_le_left ≫ K.lift i j =
      (S.CS B).homOfLE (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
          S.VT B (K.U i) ⊓ S.VT B (K.U j) ⊓ S.VT B (K.U k) ≤
            S.VT B (K.U i) ⊓ S.VT B (K.U k)) ≫ K.lift i k := by
    rw [← cancel_mono (K.κ i), Category.assoc, lift_κ, reassoc_of% h₁, lift_κ, Category.assoc,
      lift_κ, Scheme.homOfLE_homOfLE_assoc, Scheme.homOfLE_homOfLE_assoc]
  rw [show K.θS i j = K.lift i j ≫ (S.VT B (K.U i)).ι from rfl,
    show K.θS i k = K.lift i k ≫ (S.VT B (K.U i)).ι from rfl, reassoc_of% h₂]

/-- The transition data of the charts on the reduced constant scheme. -/
def transitionData : Data (S.CS B) where
  J := K.J
  V i := S.VT B (K.U i)
  θ := K.θS
  pointwise := K.θS_pointwise
  self := K.θS_self
  cocycle := K.θS_cocycle

end Charts

end Setting

end Langlands.AbelianScheme.ArtinianConstantCharts
