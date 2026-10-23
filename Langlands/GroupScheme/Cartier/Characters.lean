import Langlands.GroupScheme.Cartier.Restriction
import Langlands.GroupScheme.Multiplicative

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Cartier
universe u
variable {S : Scheme.{u}}

/-- Cartier characters, with the multiplicative character group written additively. -/
def characters (G : CommGroupScheme S) : (Over S)ᵒᵖ ⥤ AddCommGrpCat.{u} :=
  relativeHomFunctor G (Gm S)

/-- Characters as actual homomorphisms from `G_T` to `𝔾_{m,T}`. -/
abbrev CharacterHom (G : CommGroupScheme S) (T : Over S) :=
  testBaseChange T G ⟶ Gm T.left

/-- The canonical identification with homomorphisms to the multiplicative group over `T`. -/
def characterHomEquiv (G : CommGroupScheme S) (T : Over S) :
    (characters G).obj (op T) ≃+ CharacterHom G T where
  toFun χ := χ ≫ (Gm.commBaseChangeIso T.hom).hom
  invFun χ := χ ≫ (Gm.commBaseChangeIso T.hom).inv
  left_inv χ := by simp
  right_inv χ := by simp
  map_add' χ ψ := Preadditive.add_comp _ _ _ χ ψ _

/-- The canonical multiplicative-group comparison respects iterated base change. -/
lemma gmBaseChange_comp {T T' : Over S} (a : T' ⟶ T) :
    (baseChangeCompIso (Gm S) a).hom ≫
        (GroupScheme.baseChange a.left).map (Gm.baseChangeIso T.hom).hom ≫
        (Gm.baseChangeIso a.left).hom =
      (Gm.baseChangeIso T'.hom).hom := by
  apply hom_ext_points
  intro U x
  apply (Gm.pointsEquiv T'.left U).injective
  simp only [Grp.comp_hom_hom, ← Category.assoc]
  rw [Gm.pointsEquiv_baseChangeIso_hom, Gm.pointsEquiv_baseChangeIso_hom,
    Gm.baseChangeUnitsEquiv_apply, baseChangePointsEquiv_comp,
    Gm.pointsEquiv_baseChangeIso_hom, Gm.baseChangeUnitsEquiv_apply,
    Gm.baseChangeUnitsEquiv_apply]
  apply Units.ext
  simp only [Gm.pointsEquiv_val, baseChangePointsEquiv_left, Over.comp_left, Category.assoc]
  have h := baseChangeCompIso_hom_fst_assoc (Gm S) a
    (pullback.fst (Gm S).X.hom T.hom ≫ pullback.fst Gm.overSpecZ.hom (Gm.toSpecZ S))
  rw [baseChangeProj_fst_assoc] at h
  exact congrArg (fun k => (x.left ≫ k).appTop
    ((Scheme.ΓSpecIso Gm.laurentRing).inv (LaurentPolynomial.T 1))) h

/-- Restriction in the actual `Hom_T(G_T,𝔾_{m,T})` presentation. -/
def characterHomRestrict (G : CommGroupScheme S) {T T' : Over S} (a : T' ⟶ T)
    (χ : CharacterHom G T) : CharacterHom G T' :=
  Additive.ofMul ((baseChangeCompIso G a).hom ≫
    (GroupScheme.baseChange a.left).map χ.toMul ≫ (Gm.baseChangeIso a.left).hom)

/-- The character identification intertwines restriction with actual base change. -/
lemma characterHomEquiv_restrict (G : CommGroupScheme S) {T T' : Over S} (a : T' ⟶ T)
    (χ : (characters G).obj (op T)) :
    characterHomEquiv G T' ((characters G).map a.op χ) =
      characterHomRestrict G a (characterHomEquiv G T χ) := by
  change Additive.ofMul
      (restrictGrp G (Gm S) a χ.toMul ≫ (Gm.baseChangeIso T'.hom).hom) =
    Additive.ofMul ((baseChangeCompIso G a).hom ≫
      (GroupScheme.baseChange a.left).map (χ.toMul ≫ (Gm.baseChangeIso T.hom).hom) ≫
      (Gm.baseChangeIso a.left).hom)
  congr 1
  rw [restrictGrp, ← gmBaseChange_comp a, Functor.map_comp]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

/-- Restriction of actual characters preserves the identity test-scheme map. -/
lemma characterHomRestrict_id (G : CommGroupScheme S) (T : Over S)
    (χ : CharacterHom G T) : characterHomRestrict G (𝟙 T) χ = χ := by
  obtain ⟨ψ, rfl⟩ := (characterHomEquiv G T).surjective χ
  rw [← characterHomEquiv_restrict]
  change characterHomEquiv G T (restrict G (Gm S) (𝟙 T) ψ) = _
  rw [restrict_id]

/-- Restriction of actual characters composes contravariantly. -/
lemma characterHomRestrict_comp (G : CommGroupScheme S) {T T' T'' : Over S}
    (b : T'' ⟶ T') (a : T' ⟶ T) (χ : CharacterHom G T) :
    characterHomRestrict G (b ≫ a) χ =
      characterHomRestrict G b (characterHomRestrict G a χ) := by
  obtain ⟨ψ, rfl⟩ := (characterHomEquiv G T).surjective χ
  rw [← characterHomEquiv_restrict, ← characterHomEquiv_restrict,
    ← characterHomEquiv_restrict]
  change characterHomEquiv G T'' (restrict G (Gm S) (b ≫ a) ψ) =
    characterHomEquiv G T'' (restrict G (Gm S) b (restrict G (Gm S) a ψ))
  rw [restrict_comp]

/-- Actual relative characters form a functor, using the canonical additive identification. -/
def characterHomFunctor (G : CommGroupScheme S) : (Over S)ᵒᵖ ⥤ AddCommGrpCat.{u} where
  obj T := AddCommGrpCat.of (CharacterHom G T.unop)
  map {T T'} a := AddCommGrpCat.ofHom
    ((characterHomEquiv G T'.unop).toAddMonoidHom.comp
      ((restrict G (Gm S) a.unop).comp (characterHomEquiv G T.unop).symm.toAddMonoidHom))
  map_id T := by
    ext χ
    change characterHomEquiv G T.unop
      (restrict G (Gm S) (𝟙 T.unop) ((characterHomEquiv G T.unop).symm χ)) = χ
    rw [restrict_id, AddEquiv.apply_symm_apply]
  map_comp {T T' T''} a b := by
    ext χ
    change characterHomEquiv G T''.unop (restrict G (Gm S) (b.unop ≫ a.unop)
      ((characterHomEquiv G T.unop).symm χ)) =
      characterHomEquiv G T''.unop (restrict G (Gm S) b.unop
        ((characterHomEquiv G T'.unop).symm (characterHomEquiv G T'.unop
          (restrict G (Gm S) a.unop ((characterHomEquiv G T.unop).symm χ)))))
    rw [AddEquiv.symm_apply_apply, restrict_comp]

/-- The functor map is pullback of actual homomorphisms with canonical comparisons. -/
lemma characterHomFunctor_map_apply (G : CommGroupScheme S) {T T' : Over S} (a : T' ⟶ T)
    (χ : CharacterHom G T) :
    (characterHomFunctor G).map a.op χ = characterHomRestrict G a χ := by
  change characterHomEquiv G T'
    ((characters G).map a.op ((characterHomEquiv G T).symm χ)) = _
  rw [characterHomEquiv_restrict, AddEquiv.apply_symm_apply]

/-- A natural isomorphism to the actual functor `T ↦ Hom_T(G_T,𝔾_{m,T})`. -/
def characterHomNatIso (G : CommGroupScheme S) : characters G ≅ characterHomFunctor G :=
  NatIso.ofComponents (fun T => (characterHomEquiv G T.unop).toAddCommGrpIso)
    (by
      intro T T' a
      ext χ
      change characterHomEquiv G T'.unop (restrict G (Gm S) a.unop χ) =
        characterHomEquiv G T'.unop
          (restrict G (Gm S) a.unop
            ((characterHomEquiv G T.unop).symm (characterHomEquiv G T.unop χ)))
      rw [AddEquiv.symm_apply_apply])

/-- Precomposition makes Cartier characters contravariant in the group scheme. -/
def charactersMap {G' G : CommGroupScheme S} (φ : G' ⟶ G) :
    characters G ⟶ characters G' :=
  precomposeNatTrans (Gm S) φ

@[simp] lemma charactersMap_id (G : CommGroupScheme S) :
    charactersMap (𝟙 G) = 𝟙 (characters G) :=
  precomposeNatTrans_id (Gm S) G

lemma charactersMap_comp {G'' G' G : CommGroupScheme S} (ψ : G'' ⟶ G') (φ : G' ⟶ G) :
    charactersMap (ψ ≫ φ) = charactersMap φ ≫ charactersMap ψ :=
  precomposeNatTrans_comp (Gm S) ψ φ

/-- Precomposition in the actual relative-Hom presentation. -/
lemma characterHomEquiv_precompose {G' G : CommGroupScheme S} (φ : G' ⟶ G)
    (T : Over S) (χ : (characters G).obj (op T)) :
    characterHomEquiv G' T ((charactersMap φ).app (op T) χ) =
      (CommGroupScheme.baseChange T.hom).map φ ≫ characterHomEquiv G T χ :=
by
  change ((CommGroupScheme.baseChange T.hom).map φ ≫ χ) ≫
    (Gm.commBaseChangeIso T.hom).hom =
      (CommGroupScheme.baseChange T.hom).map φ ≫ χ ≫ (Gm.commBaseChangeIso T.hom).hom
  exact Category.assoc _ _ _

/-- The intrinsic evaluation pairing, with values in the actual multiplicative group scheme. -/
def characterEvaluation {G : CommGroupScheme S} {T : Over S}
    (χ : (characters G).obj (op T)) : (T ⟶ G.X) →* (T ⟶ (Gm S).X) :=
  evaluation χ

/-- In the `Hom_T(G_T,𝔾_{m,T})` presentation, evaluation applies the character to a section. -/
lemma characterEvaluation_section {G : CommGroupScheme S} {T : Over S}
    (χ : (characters G).obj (op T)) (x : T ⟶ G.X) :
    Gm.pointsEquiv T.left (Over.mk (𝟙 T.left))
      ((sectionPointsEquiv G T).symm x ≫ (characterHomEquiv G T χ).toMul.hom.hom) =
        Gm.pointsEquiv S T (characterEvaluation χ x) := by
  change Gm.pointsEquiv T.left (Over.mk (𝟙 T.left))
    (((sectionPointsEquiv G T).symm x ≫ χ.toMul.hom.hom) ≫
      (Gm.baseChangeIso T.hom).hom.hom.hom) = _
  rw [Gm.pointsEquiv_baseChangeIso_hom, Gm.baseChangeUnitsEquiv_apply]
  apply Units.ext
  simp only [Gm.pointsEquiv_val, baseChangePointsEquiv_left]
  have h := sectionPointsEquiv_left (Gm S) T
    ((sectionPointsEquiv G T).symm x ≫ χ.toMul.hom.hom)
  exact congrArg (fun k => (k ≫ pullback.fst Gm.overSpecZ.hom (Gm.toSpecZ S)).appTop
    ((Scheme.ΓSpecIso Gm.laurentRing).inv (LaurentPolynomial.T 1))) h.symm

@[simp] lemma characterEvaluation_one {G : CommGroupScheme S} {T : Over S}
    (χ : (characters G).obj (op T)) : characterEvaluation χ 1 = 1 :=
  evaluation_one χ

@[simp] lemma characterEvaluation_mul {G : CommGroupScheme S} {T : Over S}
    (χ : (characters G).obj (op T)) (x y : T ⟶ G.X) :
    characterEvaluation χ (x * y) = characterEvaluation χ x * characterEvaluation χ y :=
  evaluation_mul χ x y

@[simp] lemma characterEvaluation_inv {G : CommGroupScheme S} {T : Over S}
    (χ : (characters G).obj (op T)) (x : T ⟶ G.X) :
    characterEvaluation χ x⁻¹ = (characterEvaluation χ x)⁻¹ :=
  evaluation_inv χ x

@[simp] lemma characterEvaluation_zero {G : CommGroupScheme S} {T : Over S} (x : T ⟶ G.X) :
    characterEvaluation (0 : (characters G).obj (op T)) x = 1 :=
  evaluation_zero x

@[simp] lemma characterEvaluation_add {G : CommGroupScheme S} {T : Over S}
    (χ ψ : (characters G).obj (op T)) (x : T ⟶ G.X) :
    characterEvaluation (χ + ψ) x = characterEvaluation χ x * characterEvaluation ψ x :=
  evaluation_add χ ψ x

@[simp] lemma characterEvaluation_neg {G : CommGroupScheme S} {T : Over S}
    (χ : (characters G).obj (op T)) (x : T ⟶ G.X) :
    characterEvaluation (-χ) x = (characterEvaluation χ x)⁻¹ :=
  evaluation_neg χ x

lemma characterEvaluation_restrict {G : CommGroupScheme S} {T T' : Over S} (a : T' ⟶ T)
    (χ : (characters G).obj (op T)) (x : T ⟶ G.X) :
    characterEvaluation ((characters G).map a.op χ) (a ≫ x) =
      a ≫ characterEvaluation χ x :=
  evaluation_restrict a χ x

lemma characterEvaluation_precompose {G' G : CommGroupScheme S} (φ : G' ⟶ G)
    {T : Over S} (χ : (characters G).obj (op T)) (x : T ⟶ G'.X) :
    characterEvaluation ((charactersMap φ).app (op T) χ) x =
      characterEvaluation χ (x ≫ φ.toMul.hom.hom) :=
  evaluation_precompose φ χ x

/-- Under `[n]_G=0`, evaluation factors canonically through the actual kernel `μ_n`. -/
def muEvaluation {G : CommGroupScheme S} (n : ℕ)
    (h : multiplication G.toGrp (n : ℤ) = 1) {T : Over S}
    (χ : (characters G).obj (op T)) (x : T ⟶ G.X) : T ⟶ (mu S n).X :=
  torsionEvaluation n h χ x

@[simp] lemma muEvaluation_incl {G : CommGroupScheme S} (n : ℕ)
    (h : multiplication G.toGrp (n : ℤ) = 1) {T : Over S}
    (χ : (characters G).obj (op T)) (x : T ⟶ G.X) :
    muEvaluation n h χ x ≫ (mu.incl S n).toMul.hom.hom = characterEvaluation χ x :=
  torsionEvaluation_ι n h χ x

lemma muEvaluation_unique {G : CommGroupScheme S} (n : ℕ)
    (h : multiplication G.toGrp (n : ℤ) = 1) {T : Over S}
    (χ : (characters G).obj (op T)) (x : T ⟶ G.X) (y : T ⟶ (mu S n).X)
    (hy : y ≫ (mu.incl S n).toMul.hom.hom = characterEvaluation χ x) :
    y = muEvaluation n h χ x :=
  torsionEvaluation_unique n h χ x y hy

lemma muEvaluation_restrict {G : CommGroupScheme S} (n : ℕ)
    (h : multiplication G.toGrp (n : ℤ) = 1) {T T' : Over S} (a : T' ⟶ T)
    (χ : (characters G).obj (op T)) (x : T ⟶ G.X) :
    muEvaluation n h ((characters G).map a.op χ) (a ≫ x) = a ≫ muEvaluation n h χ x :=
  torsionEvaluation_restrict n h a χ x

lemma muEvaluation_precompose {G' G : CommGroupScheme S} (φ : G' ⟶ G) (n : ℕ)
    (h : multiplication G.toGrp (n : ℤ) = 1)
    (h' : multiplication G'.toGrp (n : ℤ) = 1) {T : Over S}
    (χ : (characters G).obj (op T)) (x : T ⟶ G'.X) :
    muEvaluation n h' ((charactersMap φ).app (op T) χ) x =
      muEvaluation n h χ (x ≫ φ.toMul.hom.hom) :=
  torsionEvaluation_precompose (Gm S) φ n h h' χ x

@[simp] lemma muEvaluation_one {G : CommGroupScheme S} (n : ℕ)
    (h : multiplication G.toGrp (n : ℤ) = 1) {T : Over S}
    (χ : (characters G).obj (op T)) :
    muEvaluation n h χ 1 = 1 :=
  torsionEvaluation_one n h χ

@[simp] lemma muEvaluation_mul {G : CommGroupScheme S} (n : ℕ)
    (h : multiplication G.toGrp (n : ℤ) = 1) {T : Over S}
    (χ : (characters G).obj (op T)) (x y : T ⟶ G.X) :
    muEvaluation n h χ (x * y) = muEvaluation n h χ x * muEvaluation n h χ y :=
  torsionEvaluation_mul n h χ x y

@[simp] lemma muEvaluation_inv {G : CommGroupScheme S} (n : ℕ)
    (h : multiplication G.toGrp (n : ℤ) = 1) {T : Over S}
    (χ : (characters G).obj (op T)) (x : T ⟶ G.X) :
    muEvaluation n h χ x⁻¹ = (muEvaluation n h χ x)⁻¹ :=
  torsionEvaluation_inv n h χ x

@[simp] lemma muEvaluation_add {G : CommGroupScheme S} (n : ℕ)
    (h : multiplication G.toGrp (n : ℤ) = 1) {T : Over S}
    (χ : (characters G).obj (op T)) (ψ : (characters G).obj (op T)) (x : T ⟶ G.X) :
    muEvaluation n h (χ + ψ) x = muEvaluation n h χ x * muEvaluation n h ψ x :=
  torsionEvaluation_add n h χ ψ x

@[simp] lemma muEvaluation_neg {G : CommGroupScheme S} (n : ℕ)
    (h : multiplication G.toGrp (n : ℤ) = 1) {T : Over S}
    (χ : (characters G).obj (op T)) (x : T ⟶ G.X) :
    muEvaluation n h (-χ) x = (muEvaluation n h χ x)⁻¹ :=
  torsionEvaluation_neg n h χ x

@[simp] lemma muEvaluation_zero {G : CommGroupScheme S} (n : ℕ)
    (h : multiplication G.toGrp (n : ℤ) = 1) {T : Over S} (x : T ⟶ G.X) :
    muEvaluation n h (0 : (characters G).obj (op T)) x = 1 :=
  torsionEvaluation_zero n h x

/-- The same intrinsic pairing interpreted as a root of unity in global sections. -/
def rootsEvaluation {G : CommGroupScheme S} (n : ℕ)
    (h : multiplication G.toGrp (n : ℤ) = 1) {T : Over S}
    (χ : (characters G).obj (op T)) (x : T ⟶ G.X) : rootsOfUnity n Γ(T.left, ⊤) :=
  mu.pointsEquiv S n T (muEvaluation n h χ x)

@[simp] lemma rootsEvaluation_val {G : CommGroupScheme S} (n : ℕ)
    (h : multiplication G.toGrp (n : ℤ) = 1) {T : Over S}
    (χ : (characters G).obj (op T)) (x : T ⟶ G.X) :
    (rootsEvaluation n h χ x : Γ(T.left, ⊤)ˣ) =
      Gm.pointsEquiv S T (characterEvaluation χ x) := by
  rw [rootsEvaluation, mu.pointsEquiv_val]
  exact congrArg (Gm.pointsEquiv S T) (muEvaluation_incl n h χ x)

lemma rootsEvaluation_restrict {G : CommGroupScheme S} (n : ℕ)
    (h : multiplication G.toGrp (n : ℤ) = 1) {T T' : Over S} (a : T' ⟶ T)
    (χ : (characters G).obj (op T)) (x : T ⟶ G.X) :
    rootsEvaluation n h ((characters G).map a.op χ) (a ≫ x) =
      restrictRootsOfUnity a.left.appTop.hom n (rootsEvaluation n h χ x) := by
  rw [rootsEvaluation, muEvaluation_restrict, mu.pointsEquiv_naturality]
  rfl

/-- On an affine test scheme, intrinsic evaluation is an element of `rootsOfUnity n R`. -/
def affineRootsEvaluation {G : CommGroupScheme S} (n : ℕ)
    (h : multiplication G.toGrp (n : ℤ) = 1) {R : CommRingCat.{u}} (f : Spec R ⟶ S)
    (χ : (characters G).obj (op (Over.mk f))) (x : Over.mk f ⟶ G.X) : rootsOfUnity n R :=
  mu.affinePointsEquiv n f (muEvaluation n h χ x)

@[simp] lemma affineRootsEvaluation_val {G : CommGroupScheme S} (n : ℕ)
    (h : multiplication G.toGrp (n : ℤ) = 1) {R : CommRingCat.{u}} (f : Spec R ⟶ S)
    (χ : (characters G).obj (op (Over.mk f))) (x : Over.mk f ⟶ G.X) :
    (affineRootsEvaluation n h f χ x : Rˣ) =
      Gm.affinePointsEquiv f (characterEvaluation χ x) := by
  rw [affineRootsEvaluation, mu.affinePointsEquiv_val]
  exact congrArg (Gm.affinePointsEquiv f) (muEvaluation_incl n h χ x)

/-- Affine evaluation commutes with every ring homomorphism. -/
lemma affineRootsEvaluation_naturality {G : CommGroupScheme S} (n : ℕ)
    (h : multiplication G.toGrp (n : ℤ) = 1) {R R' : CommRingCat.{u}}
    (φ : R ⟶ R') (f : Spec R ⟶ S)
    (χ : (characters G).obj (op (Over.mk f))) (x : Over.mk f ⟶ G.X) :
    affineRootsEvaluation n h (Spec.map φ ≫ f)
        ((characters G).map (Gm.affineMap φ f).op χ) (Gm.affineMap φ f ≫ x) =
      restrictRootsOfUnity φ.hom n (affineRootsEvaluation n h f χ x) := by
  rw [affineRootsEvaluation, muEvaluation_restrict, mu.affinePointsEquiv_naturality]
  rfl

end Langlands.GroupScheme.Cartier
