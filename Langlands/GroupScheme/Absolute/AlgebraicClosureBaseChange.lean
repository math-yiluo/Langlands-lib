import Langlands.GroupScheme.Torus.CocharacterSplitting
import Langlands.GroupScheme.Absolute.BorelTransport
import Langlands.GroupScheme.SubgroupBaseChange
import Langlands.GroupScheme.Reductive.GeneralLinear
import Langlands.GroupScheme.GeometricConnectedness
import Langlands.GroupScheme.Absolute.SolvableBijectiveBaseChange

/-! # Base change along an isomorphism of fields -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section Retraction

variable {S S' : Scheme.{u}} (e : S' ⟶ S) (c : S ⟶ S')

/-- Precomposition with a morphism of test schemes, as a homomorphism of point groups. -/
def precompHom {T T' : Over S} (a : T' ⟶ T) (G : GroupScheme S) :
    (T ⟶ G.X) →* (T' ⟶ G.X) where
  toFun x := a ≫ x
  map_one' := MonObj.comp_one a
  map_mul' x y := MonObj.comp_mul a x y

/-- Precomposition with an isomorphism of test schemes, as an isomorphism of point groups. -/
abbrev precompEquiv {T T' : Over S} (a : T' ≅ T) (G : GroupScheme S) :
    (T ⟶ G.X) ≃* (T' ⟶ G.X) :=
  CocharacterSplitting.precompEquiv (G := G) a

variable {e c}

/-- If `c ≫ e = 𝟙`, a test scheme over `S` is unchanged by moving it to `S'` along `c` and
back along `e`. -/
def overMapRetractionIso (h : c ≫ e = 𝟙 S) (T : Over S) :
    (Over.map e).obj ((Over.map c).obj T) ≅ T :=
  Over.isoMk (Iso.refl _) (by simp [Category.assoc, h])

@[simp] theorem overMapRetractionIso_hom_left (h : c ≫ e = 𝟙 S) (T : Over S) :
    (overMapRetractionIso h T).hom.left = 𝟙 T.left := rfl

@[simp] theorem overMapRetractionIso_inv_left (h : c ≫ e = 𝟙 S) (T : Over S) :
    (overMapRetractionIso h T).inv.left = 𝟙 T.left := rfl

/-- The points of the base change along `c` of the base change along `e` of `G` are the points
of `G`, when `c ≫ e = 𝟙`. -/
def retractionPointsEquiv (h : c ≫ e = 𝟙 S) (G : GroupScheme S) (T : Over S) :
    (T ⟶ ((GroupScheme.baseChange c).obj ((GroupScheme.baseChange e).obj G)).X) ≃*
      (T ⟶ G.X) :=
  ((baseChangePointsEquiv c ((GroupScheme.baseChange e).obj G) T).trans
    (baseChangePointsEquiv e G ((Over.map c).obj T))).trans
      (precompEquiv (overMapRetractionIso h T).symm G)

theorem retractionPointsEquiv_naturality (h : c ≫ e = 𝟙 S) (G : GroupScheme S)
    {T T' : Over S} (a : T' ⟶ T)
    (x : T ⟶ ((GroupScheme.baseChange c).obj ((GroupScheme.baseChange e).obj G)).X) :
    retractionPointsEquiv h G T' (a ≫ x) = a ≫ retractionPointsEquiv h G T x := by
  simp only [retractionPointsEquiv, MulEquiv.trans_apply, baseChangePointsEquiv_naturality]
  change (overMapRetractionIso h T').inv ≫ (Over.map e).map ((Over.map c).map a) ≫ _ =
    a ≫ (overMapRetractionIso h T).inv ≫ _
  rw [← Category.assoc, ← Category.assoc]
  congr 1

/-- Base change along `e` followed by base change along a section `c` of it is the identity. -/
def baseChangeRetractionIso (h : c ≫ e = 𝟙 S) (G : GroupScheme S) :
    (GroupScheme.baseChange c).obj ((GroupScheme.baseChange e).obj G) ≅ G :=
  isoOfPoints (retractionPointsEquiv h G) (retractionPointsEquiv_naturality h G)

theorem comp_baseChangeRetractionIso_hom (h : c ≫ e = 𝟙 S) (G : GroupScheme S) (T : Over S)
    (x : T ⟶ ((GroupScheme.baseChange c).obj ((GroupScheme.baseChange e).obj G)).X) :
    x ≫ (baseChangeRetractionIso h G).hom.hom.hom = retractionPointsEquiv h G T x :=
  comp_isoOfPoints_hom _ _ T x

theorem comp_baseChangeRetractionIso_inv (h : c ≫ e = 𝟙 S) (G : GroupScheme S) (T : Over S)
    (y : T ⟶ G.X) :
    y ≫ (baseChangeRetractionIso h G).inv.hom.hom = (retractionPointsEquiv h G T).symm y :=
  comp_isoOfPoints_inv _ _ T y

theorem baseChangeRetractionIso_hom_naturality (h : c ≫ e = 𝟙 S) {G H : GroupScheme S}
    (f : G ⟶ H) :
    (GroupScheme.baseChange c).map ((GroupScheme.baseChange e).map f) ≫
        (baseChangeRetractionIso h H).hom =
      (baseChangeRetractionIso h G).hom ≫ f := by
  apply hom_ext_points
  intro T x
  rw [Grp.comp_hom_hom, Grp.comp_hom_hom, ← Category.assoc, ← Category.assoc,
    comp_baseChangeRetractionIso_hom, comp_baseChangeRetractionIso_hom]
  simp only [retractionPointsEquiv, MulEquiv.trans_apply, baseChangePointsEquiv_comp]
  rfl

/-- Base change along `e` reflects triviality of ranges when `e` has a section `c`. -/
theorem range_eq_bot_of_range_baseChange_eq_bot (h : c ≫ e = 𝟙 S) {H G : GroupScheme S}
    (f : H ⟶ G) (hf : SubgroupFunctor.range ((GroupScheme.baseChange e).map f) = ⊥) :
    SubgroupFunctor.range f = ⊥ := by
  have h₁ : SubgroupFunctor.range
      ((GroupScheme.baseChange c).map ((GroupScheme.baseChange e).map f)) = ⊥ := by
    rw [SubgroupFunctor.range_baseChangeHom, hf, SubgroupFunctor.bot_baseChange]
  apply SubgroupFunctor.ext
  intro T
  rw [SubgroupFunctor.bot_carrier, Subgroup.eq_bot_iff_forall]
  rintro x ⟨y, rfl⟩
  change T ⟶ H.X at y
  have hy : (y ≫ (baseChangeRetractionIso h H).inv.hom.hom) ≫
      ((GroupScheme.baseChange c).map ((GroupScheme.baseChange e).map f)).hom.hom ∈
        (SubgroupFunctor.range
          ((GroupScheme.baseChange c).map ((GroupScheme.baseChange e).map f))).carrier T :=
    ⟨_, rfl⟩
  rw [h₁, SubgroupFunctor.bot_carrier, Subgroup.mem_bot] at hy
  have hf' : f = (baseChangeRetractionIso h H).inv ≫
      (GroupScheme.baseChange c).map ((GroupScheme.baseChange e).map f) ≫
        (baseChangeRetractionIso h G).hom := by
    rw [baseChangeRetractionIso_hom_naturality, Iso.inv_hom_id_assoc]
  change y ≫ f.hom.hom = 1
  rw [hf', Grp.comp_hom_hom, Grp.comp_hom_hom, ← Category.assoc, ← Category.assoc, hy,
    MonObj.one_comp]

/-- Base change along `e` reflects isomorphisms when `e` has a section `c`. -/
theorem isIso_of_isIso_baseChange (h : c ≫ e = 𝟙 S) {H G : GroupScheme S} (f : H ⟶ G)
    (hf : IsIso ((GroupScheme.baseChange e).map f)) : IsIso f := by
  have hf' : f = (baseChangeRetractionIso h H).inv ≫
      (GroupScheme.baseChange c).map ((GroupScheme.baseChange e).map f) ≫
        (baseChangeRetractionIso h G).hom := by
    rw [baseChangeRetractionIso_hom_naturality, Iso.inv_hom_id_assoc]
  rw [hf']
  infer_instance

end Retraction

/-- Base change along an isomorphism of schemes preserves connectedness. -/
theorem connectedSpace_baseChange_of_isIso {S S' : Scheme.{u}} (b : S' ⟶ S) [IsIso b]
    (G : GroupScheme S) [ConnectedSpace G.X.left] :
    ConnectedSpace ((GroupScheme.baseChange b).obj G).X.left := by
  exact (Scheme.homeoOfIso (asIso (pullback.fst G.X.hom b))).symm.connectedSpace_iff.mp ‹_›

section Field

variable {K K' : Type u} [Field K] [Field K']

/-- Moving a test scheme along `Spec φ` composes its structure ring map with `φ`. -/
theorem scalarMap_overMap_specMap (φ : K →+* K') (T : Over (Spec (CommRingCat.of K'))) (a : K) :
    scalarMap ((Over.map (Spec.map (CommRingCat.ofHom φ))).obj T) a = scalarMap T (φ a) := by
  change ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫
      (T.hom ≫ Spec.map (CommRingCat.ofHom φ)).appTop).hom a =
    ((Scheme.ΓSpecIso (CommRingCat.of K')).inv ≫ T.hom.appTop).hom (φ a)
  rw [Scheme.Hom.comp_appTop, ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality]
  rfl

/-- `Spec` of the inverse of a bijective field map is a section of `Spec` of the map. -/
theorem specMap_symm_comp_specMap (φ : K →+* K') (hφ : Function.Bijective φ) :
    Spec.map (CommRingCat.ofHom ((RingEquiv.ofBijective φ hφ).symm : K' →+* K)) ≫
      Spec.map (CommRingCat.ofHom φ) = 𝟙 _ := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  convert Spec.map_id (CommRingCat.of K)
  ext a
  exact (RingEquiv.ofBijective φ hφ).symm_apply_apply a

theorem specMap_comp_specMap_symm (φ : K →+* K') (hφ : Function.Bijective φ) :
    Spec.map (CommRingCat.ofHom φ) ≫
      Spec.map (CommRingCat.ofHom ((RingEquiv.ofBijective φ hφ).symm : K' →+* K)) = 𝟙 _ := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  convert Spec.map_id (CommRingCat.of K')
  ext a
  exact (RingEquiv.ofBijective φ hφ).apply_symm_apply a

/-- Base change along a bijective map of fields preserves unipotence. -/
theorem IsUnipotent.baseChange_of_bijective (φ : K →+* K') (hφ : Function.Bijective φ)
    {H : GroupScheme (Spec (CommRingCat.of K))} (hH : IsUnipotent H) :
    IsUnipotent ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom φ))).obj H) := by
  set e := Spec.map (CommRingCat.ofHom φ)
  set c := Spec.map (CommRingCat.ofHom ((RingEquiv.ofBijective φ hφ).symm : K' →+* K))
  have h : c ≫ e = 𝟙 _ := specMap_symm_comp_specMap φ hφ
  have h' : e ≫ c = 𝟙 _ := specMap_comp_specMap_symm φ hφ
  intro n _ _ _ ρ
  let ρ₀ : MatrixRepresentation H n := (baseChangeRetractionIso h H).inv ≫
    (GroupScheme.baseChange c).map ρ ≫ (GeneralLinear.baseChangeIso n c).hom
  obtain ⟨v, hv, hfix⟩ := hH n ρ₀
  refine ⟨fun i => φ (v i), ?_, ?_⟩
  · intro h0
    apply hv
    funext i
    exact hφ.1 (by simpa using congrFun h0 i)
  intro T g
  let T₀ := (Over.map e).obj T
  let g₀ := baseChangePointsEquiv e H T g
  let k := overMapRetractionIso h' T
  have hpt : baseChangePointsEquiv c ((GroupScheme.baseChange e).obj H) T₀
      ((retractionPointsEquiv h H T₀).symm g₀) = k.hom ≫ g := by
    have : retractionPointsEquiv h H T₀
        ((baseChangePointsEquiv c ((GroupScheme.baseChange e).obj H) T₀).symm (k.hom ≫ g)) =
          g₀ := by
      simp only [retractionPointsEquiv, MulEquiv.trans_apply, MulEquiv.apply_symm_apply,
        baseChangePointsEquiv_naturality]
      change (overMapRetractionIso h T₀).inv ≫ (Over.map e).map k.hom ≫ g₀ = g₀
      have hk : (overMapRetractionIso h T₀).inv ≫ (Over.map e).map k.hom = 𝟙 T₀ := by
        apply Over.OverMorphism.ext
        simp [k]
        rfl
      rw [← Category.assoc, hk, Category.id_comp]
    rw [← this, MulEquiv.symm_apply_apply, MulEquiv.apply_symm_apply]
  have key : ρ₀.pointMatrix T₀ g₀ = ρ.pointMatrix T g := by
    rw [MatrixRepresentation.pointMatrix_apply]
    simp only [ρ₀, Grp.comp_hom_hom]
    rw [← Category.assoc, comp_baseChangeRetractionIso_inv, ← Category.assoc,
      GeneralLinear.baseChangeIso, comp_isoOfPoints_hom]
    simp only [GeneralLinear.baseChangeGLPointsEquiv, MulEquiv.trans_apply,
      MulEquiv.apply_symm_apply, baseChangePointsEquiv_comp, hpt]
    rw [← MatrixRepresentation.pointMatrix_apply, MatrixRepresentation.pointMatrix_naturality]
    simp [k, Matrix.GeneralLinearGroup.map_id]
  have hs : ∀ a, scalarMap ((Over.map e).obj T) a = scalarMap T (φ a) :=
    scalarMap_overMap_specMap φ T
  have hT := hfix T₀ g₀
  rw [key] at hT
  simp only [T₀, hs] at hT
  exact hT

/-- Base change along a bijective map of fields preserves triviality of the unipotent radical. -/
theorem HasTrivialUnipotentRadical.baseChange_of_bijective (φ : K →+* K')
    (hφ : Function.Bijective φ) {G : GroupScheme (Spec (CommRingCat.of K))}
    (hG : HasTrivialUnipotentRadical G) :
    HasTrivialUnipotentRadical
      ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom φ))).obj G) := by
  have h := specMap_symm_comp_specMap φ hφ
  have h' := specMap_comp_specMap_symm φ hφ
  have : IsIso (Spec.map (CommRingCat.ofHom
      ((RingEquiv.ofBijective φ hφ).symm : K' →+* K))) := ⟨⟨_, h, h'⟩⟩
  have hG' := hG.of_iso (baseChangeRetractionIso h G)
  intro H i hC hS hCon hU hN
  refine range_eq_bot_of_range_baseChange_eq_bot h' i (hG' _ _ (hC.baseChange _) ?_
    (connectedSpace_baseChange_of_isIso _ H)
    (IsUnipotent.baseChange_of_bijective _ (RingEquiv.ofBijective φ hφ).symm.bijective hU) ?_)
  · exact inferInstanceAs (Smooth (pullback.snd H.X.hom _))
  · rw [SubgroupFunctor.range_baseChangeHom]
    exact hN.baseChange _

/-- Base change along a bijective map of fields preserves the Borel property. -/
theorem IsBorelSubgroup.baseChange_of_bijective (φ : K →+* K') (hφ : Function.Bijective φ)
    {B G : GroupScheme (Spec (CommRingCat.of K))} {j : B ⟶ G} (hj : IsBorelSubgroup j) :
    IsBorelSubgroup ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom φ))).map j) := by
  have h := specMap_symm_comp_specMap φ hφ
  have h' := specMap_comp_specMap_symm φ hφ
  have : IsIso (Spec.map (CommRingCat.ofHom
      ((RingEquiv.ofBijective φ hφ).symm : K' →+* K))) := ⟨⟨_, h, h'⟩⟩
  have : IsIso (Spec.map (CommRingCat.ofHom φ)) := ⟨⟨_, h', h⟩⟩
  have := hj.smooth
  have := hj.connectedSpace
  refine ⟨hj.isClosedSubgroup.baseChange _, inferInstanceAs (Smooth (pullback.snd B.X.hom _)),
    connectedSpace_baseChange_of_isIso _ B,
    IsSolvableGroupScheme.baseChange_of_bijective φ hφ hj.isSolvableGroupScheme, ?_⟩
  intro B' i' f hC hS hCon hSol hf
  have hB := hj.comp_iso (baseChangeRetractionIso h G).symm
  have hnat := baseChangeRetractionIso_hom_naturality h j
  have hmax := hB.maximal _
    ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom
      ((RingEquiv.ofBijective φ hφ).symm : K' →+* K)))).map i')
    ((baseChangeRetractionIso h B).inv ≫ (GroupScheme.baseChange (Spec.map (CommRingCat.ofHom
      ((RingEquiv.ofBijective φ hφ).symm : K' →+* K)))).map f)
    (hC.baseChange _) (inferInstanceAs (Smooth (pullback.snd B'.X.hom _)))
    (connectedSpace_baseChange_of_isIso _ B')
    (IsSolvableGroupScheme.baseChange_of_bijective _
      (RingEquiv.ofBijective φ hφ).symm.bijective hSol) (by
      rw [Category.assoc, ← Functor.map_comp, hf, Iso.symm_hom, Iso.inv_comp_eq,
        ← cancel_mono (baseChangeRetractionIso h G).hom, Category.assoc, Category.assoc,
        Iso.inv_hom_id, Category.comp_id, hnat])
  have : IsIso ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom
      ((RingEquiv.ofBijective φ hφ).symm : K' →+* K)))).map f) := by
    rw [← Iso.hom_inv_id_assoc (baseChangeRetractionIso h B) ((GroupScheme.baseChange
      (Spec.map (CommRingCat.ofHom ((RingEquiv.ofBijective φ hφ).symm : K' →+* K)))).map f)]
    infer_instance
  exact isIso_of_isIso_baseChange h' f this

end Field

section AlgebraicClosure

variable {k : Type u} [Field k]

theorem bijective_algebraMap_algebraicClosure_algebraicClosure :
    Function.Bijective (algebraMap (AlgebraicClosure k) (AlgebraicClosure (AlgebraicClosure k))) :=
  IsAlgClosed.algebraMap_bijective_of_isIntegral

/-- The base change of a connected reductive group to an algebraic closure is connected
reductive. -/
theorem IsConnectedReductive.baseChange_toAlgebraicClosure
    {G : GroupScheme (Spec (CommRingCat.of k))} (hG : IsConnectedReductive G) :
    IsConnectedReductive ((GroupScheme.baseChange (toAlgebraicClosure k)).obj G) := by
  have := hG.smooth
  have := hG.isAffineHom
  exact ⟨inferInstanceAs (Smooth (pullback.snd G.X.hom _)),
    inferInstanceAs (IsAffineHom (pullback.snd G.X.hom _)),
    hG.connectedSpace_toAlgebraicClosure,
    HasTrivialUnipotentRadical.baseChange_of_bijective _
      bijective_algebraMap_algebraicClosure_algebraicClosure
      hG.hasTrivialGeometricUnipotentRadical⟩

/-- The base change of a parabolic subgroup to an algebraic closure is parabolic. -/
theorem IsParabolicSubgroup.baseChange_toAlgebraicClosure
    {P G : GroupScheme (Spec (CommRingCat.of k))} {j : P ⟶ G} (hj : IsParabolicSubgroup j) :
    IsParabolicSubgroup ((GroupScheme.baseChange (toAlgebraicClosure k)).map j) := by
  have := hj.smooth
  obtain ⟨B, j₀, f₀, hB, hf₀⟩ := hj.exists_isBorelSubgroup
  refine ⟨hj.isClosedSubgroup.baseChange _, inferInstanceAs (Smooth (pullback.snd P.X.hom _)),
    _, _, (GroupScheme.baseChange (toAlgebraicClosure (AlgebraicClosure k))).map f₀,
    IsBorelSubgroup.baseChange_of_bijective _
      bijective_algebraMap_algebraicClosure_algebraicClosure hB, ?_⟩
  rw [← Functor.map_comp, hf₀]

end AlgebraicClosure

end Langlands.GroupScheme
