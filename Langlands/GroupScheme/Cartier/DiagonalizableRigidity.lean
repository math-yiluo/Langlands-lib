import Langlands.GroupScheme.Cartier.DiagonalizablePoints

/-! # Local rigidity of characters of a diagonalizable group -/

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.Cartier.DiagonalizableCharacters

open RelativeMultiplicativeType

/-! ### Homomorphisms out of `ℤ` -/

/-- For a commutative group `G`, homomorphisms `Multiplicative (ULift ℤ) →* G` are the elements
of `G`: an element `u` corresponds to `n ↦ u ^ n`. -/
def zpowEquiv (G : Type v) [CommGroup G] : G ≃* (Multiplicative (ULift.{u} ℤ) →* G) :=
  (zpowersMulHom G).trans
    (MulEquiv.monoidHomCongrLeft (AddEquiv.toMultiplicative AddEquiv.ulift.symm))

@[simp]
lemma zpowEquiv_apply_one {G : Type v} [CommGroup G] (g : G) :
    zpowEquiv.{u} G g (Multiplicative.ofAdd (ULift.up 1)) = g := by
  simp [zpowEquiv]
  exact zpow_one g

lemma zpowEquiv_symm_apply {G : Type v} [CommGroup G]
    (f : Multiplicative (ULift.{u} ℤ) →* G) :
    (zpowEquiv.{u} G).symm f = f (Multiplicative.ofAdd (ULift.up 1)) := by
  conv_rhs => rw [← MulEquiv.apply_symm_apply (zpowEquiv.{u} G) f]
  rw [zpowEquiv_apply_one]

/-- Homomorphisms out of `Multiplicative (ULift ℤ)` agree when they agree on the generator. -/
lemma multiplicativeULiftInt_hom_ext {G : Type v} [CommGroup G]
    {f f' : Multiplicative (ULift.{u} ℤ) →* G}
    (h : f (Multiplicative.ofAdd (ULift.up 1)) = f' (Multiplicative.ofAdd (ULift.up 1))) :
    f = f' := by
  apply (zpowEquiv.{u} G).symm.injective
  rw [zpowEquiv_symm_apply, zpowEquiv_symm_apply, h]

lemma zpowEquiv_naturality {G H : Type v} [CommGroup G] [CommGroup H] (φ : G →* H) (g : G) :
    zpowEquiv.{u} H (φ g) = φ.comp (zpowEquiv.{u} G g) := by
  apply multiplicativeULiftInt_hom_ext
  rw [zpowEquiv_apply_one, MonoidHom.comp_apply, zpowEquiv_apply_one]

lemma addGroupFG_uliftInt : AddGroup.FG (ULift.{u} ℤ) := by
  refine AddGroup.isAddFG_iff.mpr ⟨{ULift.up 1}, ?_⟩
  rw [eq_top_iff]
  rintro ⟨n⟩ -
  have : (ULift.up n : ULift.{u} ℤ) = n • ULift.up (1 : ℤ) := by
    ext
    simp
  rw [this]
  exact AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure (by simp)) n

/-! ### `𝔾_m` as the diagonalizable group with character group `ℤ` -/

variable (X : Scheme.{u})

/-- The homomorphism of points underlying `gmDiag`. -/
def gmDiagPoints (V : Over X) :
    (V ⟶ (Gm X).X) →* (V ⟶ (diagonalizable X (ULift.{u} ℤ)).X) :=
  (pointsEquiv X (ULift.{u} ℤ) V).symm.toMonoidHom.comp
    ((zpowEquiv.{u} _).toMonoidHom.comp (Gm.pointsEquiv X V).toMonoidHom)

lemma pointsEquiv_gmDiagPoints (V : Over X) (y : V ⟶ (Gm X).X) :
    pointsEquiv X (ULift.{u} ℤ) V (gmDiagPoints X V y) =
      zpowEquiv.{u} _ (Gm.pointsEquiv X V y) :=
  MulEquiv.apply_symm_apply _ _

lemma gmDiagPoints_naturality {V V' : Over X} (a : V' ⟶ V) (y : V ⟶ (Gm X).X) :
    gmDiagPoints X V' (a ≫ y) = a ≫ gmDiagPoints X V y := by
  apply (pointsEquiv X (ULift.{u} ℤ) V').injective
  rw [pointsEquiv_gmDiagPoints, pointsEquiv_comp, pointsEquiv_gmDiagPoints,
    Gm.pointsEquiv_naturality, zpowEquiv_naturality]

/-- The homomorphism `𝔾_{m,X} → D_X(ℤ)` sending a unit `u` to the character `n ↦ u ^ n`. -/
def gmDiag : (Gm X).toGrp ⟶ diagonalizable X (ULift.{u} ℤ) :=
  homOfPoints (gmDiagPoints X) (fun a y => gmDiagPoints_naturality X a y)

lemma comp_gmDiag (V : Over X) (y : V ⟶ (Gm X).X) :
    y ≫ (gmDiag X).hom.hom = gmDiagPoints X V y :=
  comp_homOfPoints (gmDiagPoints X) (fun a y => gmDiagPoints_naturality X a y) V y

/-! ### A character as a homomorphism of diagonalizable groups -/

variable {S : Scheme.{u}} {M : Type u} [AddCommGroup M]

lemma testPointsEquiv_baseChangeIso_inv (T : Over S) (V : Over T.left)
    (s : V ⟶ (diagonalizable T.left M).X) :
    testPointsEquiv M T V (s ≫ (diagonalizableBaseChangeIso T.hom M).inv.hom.hom) =
      pointsEquiv T.left M V s :=
  (pointsEquiv_eq_baseChange T.hom V s).symm

/-- A character of `D_S(M)` over `T`, viewed as a homomorphism `D_{T}(M) → D_{T}(ℤ)` of
diagonalizable groups over `T.left`. -/
def toDiag {T : Over S} (χ : (characters (model S M)).obj (op T)) :
    diagonalizable T.left M ⟶ diagonalizable T.left (ULift.{u} ℤ) :=
  (diagonalizableBaseChangeIso T.hom M).inv ≫ Additive.toMul χ ≫
    (Gm.baseChangeIso T.hom).hom ≫ gmDiag T.left

lemma pointsEquiv_toDiag {T : Over S} (χ : (characters (model S M)).obj (op T)) (V : Over T.left)
    (s : V ⟶ (diagonalizable T.left M).X) :
    pointsEquiv T.left (ULift.{u} ℤ) V (s ≫ (toDiag χ).hom.hom) =
      zpowEquiv.{u} _ (act χ V (pointsEquiv T.left M V s)) := by
  have h1 : s ≫ (toDiag χ).hom.hom =
      ((s ≫ (diagonalizableBaseChangeIso T.hom M).inv.hom.hom ≫ (Additive.toMul χ).hom.hom) ≫
        (Gm.baseChangeIso T.hom).hom.hom.hom) ≫ (gmDiag T.left).hom.hom := by
    simp only [toDiag, Grp.comp_hom_hom, Category.assoc]
    rfl
  rw [h1, comp_gmDiag, pointsEquiv_gmDiagPoints, Gm.pointsEquiv_baseChangeIso_hom, act_apply,
    ← testPointsEquiv_baseChangeIso_inv, MulEquiv.symm_apply_apply, Category.assoc]

lemma act_eq_of_actsBy {T : Over S} (χ : (characters (model S M)).obj (op T))
    {g : ULift.{u} ℤ →+ M} {V : Over T.left} (h : ActsBy (toDiag χ) g V)
    (t : Multiplicative M →* (Γ(V.left, ⊤))ˣ) :
    act χ V t = t (Multiplicative.ofAdd (g (ULift.up 1))) := by
  obtain ⟨s, rfl⟩ := (pointsEquiv T.left M V).surjective t
  have h1 := congrArg (fun f => f (Multiplicative.ofAdd (ULift.up 1))) (h s)
  simp only [pointsEquiv_toDiag, zpowEquiv_apply_one] at h1
  rw [h1]
  rfl

/-- The character map `n ↦ n • m` from `ℤ` to `M`. -/
def zmulHom (m : M) : ULift.{u} ℤ →+ M :=
  (zmultiplesHom M m).comp AddEquiv.ulift.toAddMonoidHom

@[simp]
lemma zmulHom_apply_one (m : M) : zmulHom m (ULift.up 1) = m := by
  simp [zmulHom]
  exact one_zsmul m

/-- The evaluation character at `m` corresponds to the homomorphism `D(n ↦ n • m)`. -/
lemma toDiag_evalChar (T : Over S) (m : M) :
    toDiag (evalChar T m) = diagonalizableMap T.left (zmulHom m) := by
  apply hom_ext'
  intro V s
  rw [pointsEquiv_toDiag, pointsEquiv_diagonalizableMap]
  apply multiplicativeULiftInt_hom_ext
  rw [zpowEquiv_apply_one, act_evalChar, MonoidHom.comp_apply]
  congr 1
  simp

/-- Over a nonempty test scheme, distinct elements of `M` give distinct evaluation characters. -/
lemma evalChar_injective (T : Over S) [Nonempty T.left] :
    Function.Injective (evalChar (M := M) T) := by
  intro m m' h
  have h1 : diagonalizableMap T.left (zmulHom m) = diagonalizableMap T.left (zmulHom m') := by
    rw [← toDiag_evalChar, ← toDiag_evalChar, h]
  have h2 := DFunLike.congr_fun (diagonalizableMap_injective h1) (ULift.up 1)
  simpa using h2

/-! ### Open subschemes of a test scheme -/

/-- An open subscheme of `T.left`, as a scheme over `S`. -/
abbrev opensOver (T : Over S) (U : T.left.Opens) : Over S :=
  Over.mk (U.ι ≫ T.hom)

/-- The inclusion of `opensOver T U` into `T`. -/
abbrev opensι (T : Over S) (U : T.left.Opens) : opensOver T U ⟶ T :=
  Over.homMk U.ι

/-- The inclusion `opensOver T W ⟶ opensOver T U` for `W ≤ U`. -/
abbrev opensLE (T : Over S) {W U : T.left.Opens} (h : W ≤ U) :
    opensOver T W ⟶ opensOver T U :=
  Over.homMk (T.left.homOfLE h) (by simp)

lemma opensLE_comp_opensι (T : Over S) {W U : T.left.Opens} (h : W ≤ U) :
    opensLE T h ≫ opensι T U = opensι T W := by
  ext
  simp

/-! ### Being an evaluation character on an open -/

/-- `χ` is the evaluation character at `m` on the open `U` of `T.left`: its Cartier restriction
to `U` is `evalChar _ m`. -/
def IsEvalOn {T : Over S} (χ : (characters (model S M)).obj (op T)) (U : T.left.Opens)
    (m : M) : Prop :=
  (characters (model S M)).map (opensι T U).op χ = evalChar (opensOver T U) m

lemma isEvalOn_iff_act {T : Over S} (χ : (characters (model S M)).obj (op T))
    (U : T.left.Opens) (m : M) :
    IsEvalOn χ U m ↔ ∀ (V : Over U.toScheme) (t : Multiplicative M →* (Γ(V.left, ⊤))ˣ),
      act χ ((Over.map U.ι).obj V) t = t (Multiplicative.ofAdd m) := by
  rw [IsEvalOn, eq_evalChar_iff]
  exact forall_congr' fun V => forall_congr' fun t => by rw [act_restrict]; exact Iff.rfl

/-- On an open where `χ` is the evaluation character at `m`, `χ` acts by `t ↦ t(m)` on every
scheme over `T.left` whose structure map lands in that open. -/
lemma act_of_isEvalOn {T : Over S} {χ : (characters (model S M)).obj (op T)}
    {U : T.left.Opens} {m : M} (h : IsEvalOn χ U m) (V : Over T.left)
    (hV : Set.range V.hom ⊆ (U : Set T.left)) (t : Multiplicative M →* (Γ(V.left, ⊤))ˣ) :
    act χ V t = t (Multiplicative.ofAdd m) := by
  have hV' : Set.range V.hom ⊆ Set.range U.ι := by rwa [Scheme.Opens.range_ι]
  let V₀ : Over U.toScheme := Over.mk (IsOpenImmersion.lift U.ι V.hom hV')
  let b : V ⟶ (Over.map U.ι).obj V₀ := Over.homMk (𝟙 V.left) (by simp [V₀])
  have h1 := act_naturality χ b t
  rw [isEvalOn_iff_act] at h
  rw [h V₀ t] at h1
  exact h1

lemma IsEvalOn.mono {T : Over S} {χ : (characters (model S M)).obj (op T)}
    {W U : T.left.Opens} {m : M} (h : IsEvalOn χ U m) (hWU : W ≤ U) : IsEvalOn χ W m := by
  rw [isEvalOn_iff_act]
  intro V t
  apply act_of_isEvalOn h
  rintro _ ⟨y, rfl⟩
  exact hWU (V.hom y).2

lemma IsEvalOn.restrict {T T' : Over S} (a : T' ⟶ T) {χ : (characters (model S M)).obj (op T)}
    {U : T.left.Opens} {m : M} (h : IsEvalOn χ U m) :
    IsEvalOn ((characters (model S M)).map a.op χ) (a.left ⁻¹ᵁ U) m := by
  rw [isEvalOn_iff_act]
  intro V t
  rw [act_restrict]
  apply act_of_isEvalOn h
  rintro _ ⟨y, rfl⟩
  change ((V.hom ≫ (a.left ⁻¹ᵁ U).ι) ≫ a.left) y ∈ U
  rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
  exact (V.hom y).2

lemma IsEvalOn.add {T : Over S} {χ ψ : (characters (model S M)).obj (op T)}
    {U : T.left.Opens} {m m' : M} (h : IsEvalOn χ U m) (h' : IsEvalOn ψ U m') :
    IsEvalOn (χ + ψ) U (m + m') := by
  unfold IsEvalOn at *
  rw [map_add, h, h', evalChar_add]

lemma isEvalOn_zero {T : Over S} (U : T.left.Opens) :
    IsEvalOn (0 : (characters (model S M)).obj (op T)) U 0 := by
  unfold IsEvalOn
  rw [map_zero, evalChar_zero]

lemma isEvalOn_evalChar (T : Over S) (U : T.left.Opens) (m : M) :
    IsEvalOn (evalChar T m) U m :=
  restrict_evalChar (opensι T U) m

/-- **Uniqueness.** The exponent of a character on an open is unique near every point. -/
lemma IsEvalOn.unique {T : Over S} {χ : (characters (model S M)).obj (op T)}
    {U U' : T.left.Opens} {m m' : M} (h : IsEvalOn χ U m) (h' : IsEvalOn χ U' m')
    {x : T.left} (hx : x ∈ U) (hx' : x ∈ U') : m = m' := by
  have h1 := h.mono (inf_le_left : U ⊓ U' ≤ U)
  have h2 := h'.mono (inf_le_right : U ⊓ U' ≤ U')
  have : Nonempty (opensOver T (U ⊓ U')).left := ⟨⟨x, hx, hx'⟩⟩
  exact evalChar_injective _ (h1.symm.trans h2)

/-- **Local existence.** Every character is, near every point, an evaluation character. -/
lemma exists_isEvalOn {T : Over S} (χ : (characters (model S M)).obj (op T)) (x : T.left) :
    ∃ U : T.left.Opens, x ∈ U ∧ ∃ m : M, IsEvalOn χ U m := by
  have := addGroupFG_uliftInt.{u}
  obtain ⟨U, hx, g, hg⟩ := exists_opens_baseChange_map_eq (toDiag χ) x
  refine ⟨U, hx, g (ULift.up 1), ?_⟩
  rw [isEvalOn_iff_act]
  intro V t
  apply act_eq_of_actsBy
  apply actsBy_of_transport U.ι (toDiag χ) g V
  intro s
  rw [hg]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
  exact pointsEquiv_diagonalizableMap g V s

/-! ### The locally constant function of a character -/

/-- The value of a character at a point `x` of `T.left`: the exponent `m` of any open
neighbourhood of `x` on which the character is the evaluation character at `m`. -/
def charValue {T : Over S} (χ : (characters (model S M)).obj (op T)) (x : T.left) : M :=
  (exists_isEvalOn χ x).choose_spec.2.choose

lemma charValue_spec {T : Over S} (χ : (characters (model S M)).obj (op T)) (x : T.left) :
    ∃ U : T.left.Opens, x ∈ U ∧ IsEvalOn χ U (charValue χ x) :=
  ⟨(exists_isEvalOn χ x).choose, (exists_isEvalOn χ x).choose_spec.1,
    (exists_isEvalOn χ x).choose_spec.2.choose_spec⟩

lemma charValue_eq_of_isEvalOn {T : Over S} {χ : (characters (model S M)).obj (op T)}
    {U : T.left.Opens} {m : M} (h : IsEvalOn χ U m) {x : T.left} (hx : x ∈ U) :
    charValue χ x = m := by
  obtain ⟨U', hx', h'⟩ := charValue_spec χ x
  exact h'.unique h hx' hx

/-- The local characterization of the value of a character. -/
lemma charValue_eq_iff {T : Over S} (χ : (characters (model S M)).obj (op T)) (x : T.left)
    (m : M) : charValue χ x = m ↔ ∃ U : T.left.Opens, x ∈ U ∧ IsEvalOn χ U m := by
  constructor
  · rintro rfl
    exact charValue_spec χ x
  · rintro ⟨U, hx, h⟩
    exact charValue_eq_of_isEvalOn h hx

lemma isLocallyConstant_charValue {T : Over S} (χ : (characters (model S M)).obj (op T)) :
    IsLocallyConstant (charValue χ) := by
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  obtain ⟨U, hx, hU⟩ := charValue_spec χ x
  exact ⟨U, U.isOpen, hx, fun y hy =>
    (charValue_eq_of_isEvalOn hU hy).trans (charValue_eq_of_isEvalOn hU hx).symm⟩

/-- The locally constant `M`-valued function on `T.left` attached to a character. -/
def toLocallyConstant {T : Over S} (χ : (characters (model S M)).obj (op T)) :
    LocallyConstant T.left M :=
  ⟨charValue χ, isLocallyConstant_charValue χ⟩

lemma toLocallyConstant_apply {T : Over S} (χ : (characters (model S M)).obj (op T))
    (x : T.left) : toLocallyConstant χ x = charValue χ x := rfl

lemma toLocallyConstant_add {T : Over S} (χ ψ : (characters (model S M)).obj (op T)) :
    toLocallyConstant (χ + ψ) = toLocallyConstant χ + toLocallyConstant ψ := by
  ext x
  obtain ⟨U, hx, hU⟩ := charValue_spec χ x
  obtain ⟨U', hx', hU'⟩ := charValue_spec ψ x
  rw [LocallyConstant.add_apply, toLocallyConstant_apply, toLocallyConstant_apply,
    toLocallyConstant_apply]
  exact charValue_eq_of_isEvalOn ((hU.mono inf_le_left).add (hU'.mono inf_le_right))
    (show x ∈ U ⊓ U' from ⟨hx, hx'⟩)

lemma toLocallyConstant_zero (T : Over S) :
    toLocallyConstant (0 : (characters (model S M)).obj (op T)) = 0 := by
  ext x
  exact charValue_eq_of_isEvalOn (isEvalOn_zero ⊤) (show x ∈ (⊤ : T.left.Opens) from trivial)

lemma toLocallyConstant_evalChar (T : Over S) (m : M) :
    toLocallyConstant (evalChar T m) = LocallyConstant.const T.left m := by
  ext x
  exact charValue_eq_of_isEvalOn (isEvalOn_evalChar T ⊤ m)
    (show x ∈ (⊤ : T.left.Opens) from trivial)

lemma toLocallyConstant_restrict {T T' : Over S} (a : T' ⟶ T)
    (χ : (characters (model S M)).obj (op T)) (x : T'.left) :
    toLocallyConstant ((characters (model S M)).map a.op χ) x =
      toLocallyConstant χ (a.left x) := by
  obtain ⟨U, hx, hU⟩ := charValue_spec χ (a.left x)
  exact charValue_eq_of_isEvalOn (hU.restrict a) (show a.left x ∈ U from hx)

end Langlands.GroupScheme.Cartier.DiagonalizableCharacters
