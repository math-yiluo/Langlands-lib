import Langlands.GroupScheme.IntegralModel.CoefficientHomDescent
import Langlands.AbelianScheme.RelativeHomNeronExtension

/-! # Automatic coefficient descent from the prescribed generic map -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.GroupScheme.IntegralModel

namespace GenericCoefficientDescent

variable {B X Y Z W T : Scheme.{u}}

private def changeLeft (a : X ⟶ Z) (b : Y ⟶ Z) (i : W ⟶ X) :
    pullback (i ≫ a) b ⟶ pullback a b :=
  (pullbackRightPullbackFstIso a b i).inv ≫ pullback.snd i (pullback.fst a b)

@[reassoc] private theorem changeLeft_fst (a : X ⟶ Z) (b : Y ⟶ Z) (i : W ⟶ X) :
    changeLeft a b i ≫ pullback.fst a b = pullback.fst (i ≫ a) b ≫ i := by
  simp [changeLeft]

@[reassoc] private theorem changeLeft_snd (a : X ⟶ Z) (b : Y ⟶ Z) (i : W ⟶ X) :
    changeLeft a b i ≫ pullback.snd a b = pullback.snd (i ≫ a) b := by
  simp [changeLeft]

private theorem changeLeft_dominant (a : X ⟶ Z) (b : Y ⟶ Z) (i : W ⟶ X)
    [Flat b] [IsSchemeTheoreticallyDominant i] [QuasiCompact i] :
    IsSchemeTheoreticallyDominant (changeLeft a b i) := by
  have : IsSchemeTheoreticallyDominant (pullback.snd i (pullback.fst a b)) :=
    .of_isPullback (.of_hasPullback _ _)
  dsimp [changeLeft]
  infer_instance

private def changeRight (a : X ⟶ Z) (b : Y ⟶ Z) (i : W ⟶ Y) :
    pullback a (i ≫ b) ⟶ pullback a b :=
  (pullbackLeftPullbackSndIso a b i).inv ≫ pullback.fst (pullback.snd a b) i

@[reassoc] private theorem changeRight_fst (a : X ⟶ Z) (b : Y ⟶ Z) (i : W ⟶ Y) :
    changeRight a b i ≫ pullback.fst a b = pullback.fst a (i ≫ b) := by
  simp [changeRight]

@[reassoc] private theorem changeRight_snd (a : X ⟶ Z) (b : Y ⟶ Z) (i : W ⟶ Y) :
    changeRight a b i ≫ pullback.snd a b = pullback.snd a (i ≫ b) ≫ i := by
  simp [changeRight]

private theorem changeRight_dominant (a : X ⟶ Z) (b : Y ⟶ Z) (i : W ⟶ Y)
    [Flat a] [IsSchemeTheoreticallyDominant i] [QuasiCompact i] :
    IsSchemeTheoreticallyDominant (changeRight a b i) := by
  dsimp [changeRight]
  infer_instance

/-- Agreement after a dense generic factorization identifies the two maps on
the actual double relation. -/
theorem relation_eq_of_generic_factor
    (a : X ⟶ Z) (i : W ⟶ X) (m : Z ⟶ B) (n : Y ⟶ B)
    [Flat a] [Flat (i ≫ a)] [IsSchemeTheoreticallyDominant i] [QuasiCompact i]
    [IsSeparated n] (h : X ⟶ Y) (hh : h ≫ n = a ≫ m)
    (k : T ⟶ Z) [Mono k] (c : W ⟶ T) (g : T ⟶ Y)
    (hc : c ≫ k = i ≫ a) (hg : i ≫ h = c ≫ g) :
    pullback.fst a a ≫ h = pullback.snd a a ≫ h := by
  let j := changeRight (i ≫ a) a i ≫ changeLeft a a i
  have : IsSchemeTheoreticallyDominant (changeRight (i ≫ a) a i) :=
    changeRight_dominant _ _ _
  have : IsSchemeTheoreticallyDominant (changeLeft a a i) :=
    changeLeft_dominant _ _ _
  have : IsSchemeTheoreticallyDominant j := by dsimp [j]; infer_instance
  have hcc : pullback.fst (i ≫ a) (i ≫ a) ≫ c =
      pullback.snd (i ≫ a) (i ≫ a) ≫ c := by
    apply (cancel_mono k).mp
    simpa only [Category.assoc, hc] using
      (pullback.condition (f := i ≫ a) (g := i ≫ a))
  have hj : j ≫ (pullback.fst a a ≫ h) = j ≫ (pullback.snd a a ≫ h) := by
    simp only [j, Category.assoc, changeLeft_fst_assoc, changeLeft_snd_assoc,
      changeRight_fst_assoc, changeRight_snd_assoc]
    rw [hg, ← Category.assoc, ← Category.assoc, hcc]
  exact P2MW.S_NeronModelInfra_genericFibreRestrict_injective_of_flat_of_isSeparated.NeronModelInfra.GenericFibreRestrictInjective.ext_of_isSchemeTheoreticallyDominant_of_isSeparated
    n (pullback.fst a a ≫ a ≫ m)
    (by simp only [Category.assoc, hh])
    (by rw [Category.assoc, hh, ← Category.assoc, ← pullback.condition, Category.assoc])
    j hj

end GenericCoefficientDescent

namespace GenericCoefficientDescent

@[reassoc] private theorem map_fst {S T : Scheme.{u}} (p : T ⟶ S)
    {G H : GroupScheme S} (f : G ⟶ H) :
    ((GroupScheme.baseChange p).map f).hom.hom.left ≫ pullback.fst H.X.hom p =
      pullback.fst G.X.hom p ≫ f.hom.hom.left :=
  pullback.lift_fst _ _ _

private theorem compatible_of_relation {B S : Scheme.{u}} (p : S ⟶ B)
    {C D : GroupScheme B}
    (f : (GroupScheme.baseChange p).obj C ⟶ (GroupScheme.baseChange p).obj D)
    (hf : pullback.fst (pullback.fst C.X.hom p) (pullback.fst C.X.hom p) ≫
        f.hom.hom.left ≫ pullback.fst D.X.hom p =
      pullback.snd (pullback.fst C.X.hom p) (pullback.fst C.X.hom p) ≫
        f.hom.hom.left ≫ pullback.fst D.X.hom p) :
    Descent.Compatible (Descent.canonicalDatum p C) (Descent.canonicalDatum p D) f := by
  let a := pullback.fst ((GroupScheme.baseChange p).obj C).X.hom (Descent.fst p)
  let b := (Descent.canonicalOverlap p C).hom.hom.hom.left ≫
    pullback.fst ((GroupScheme.baseChange p).obj C).X.hom (Descent.snd p)
  have hab : a ≫ pullback.fst C.X.hom p = b ≫ pullback.fst C.X.hom p := by
    simpa only [a, b, Category.assoc] using (Descent.canonicalOverlap_fst p C).symm
  let j := pullback.lift a b hab
  have hj := congrArg (fun k => j ≫ k) hf
  have h : a ≫ f.hom.hom.left ≫ pullback.fst D.X.hom p =
      b ≫ f.hom.hom.left ≫ pullback.fst D.X.hom p := by
    simpa only [j, ← Category.assoc, pullback.lift_fst, pullback.lift_snd] using hj
  change (GroupScheme.baseChange (Descent.fst p)).map f ≫
      (Descent.canonicalOverlap p D).hom =
    (Descent.canonicalOverlap p C).hom ≫
      (GroupScheme.baseChange (Descent.snd p)).map f
  apply (cancel_mono
    (Descent.pullbackComparison p (Descent.snd p) (Descent.snd p ≫ p) rfl D).hom).mp
  apply Grp.hom_ext
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · simpa only [Grp.comp_hom_hom, Over.comp_left, Category.assoc,
      Descent.pullbackComparison_hom_fst, Descent.canonicalOverlap_fst,
      map_fst_assoc, a, b] using h
  · exact (Over.w (((GroupScheme.baseChange (Descent.fst p)).map f ≫
      (Descent.canonicalOverlap p D).hom) ≫
        (Descent.pullbackComparison p (Descent.snd p) (Descent.snd p ≫ p) rfl D).hom).hom.hom).trans
      (Over.w (((Descent.canonicalOverlap p C).hom ≫
        (GroupScheme.baseChange (Descent.snd p)).map f) ≫
          (Descent.pullbackComparison p (Descent.snd p) (Descent.snd p ≫ p) rfl D).hom).hom.hom).symm

private theorem generic_projection_dominant
    (R K : Type u) [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] {X : Scheme.{u}}
    (t : X ⟶ Spec (CommRingCat.of R)) [Flat t] :
    IsSchemeTheoreticallyDominant (pullback.fst t (Spec.algebraMap R K)) := by
  have : IsDominant (Spec.algebraMap R K) := by
    constructor
    change DenseRange (PrimeSpectrum.comap (algebraMap R K))
    have hker : RingHom.ker (algebraMap R K) ≤ nilradical R := by
      rw [(RingHom.injective_iff_ker_eq_bot _).mp (IsFractionRing.injective R K)]
      exact bot_le
    have hd := (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical
      (algebraMap R K)).mpr hker
    exact hd
  have : IsSchemeTheoreticallyDominant (Spec.algebraMap R K) :=
    IsSchemeTheoreticallyDominant.of_isDominant _
  infer_instance

end GenericCoefficientDescent

section Coefficients

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]
  {G H : GroupScheme (Spec (CommRingCat.of K))}
  {M : IntegralModel R K G} {N : IntegralModel R K H} {f : G ⟶ H}
  (A L : Type u) [CommRing A] [IsDomain A] [Field L]
  [Algebra R A] [Algebra A L] [IsFractionRing A L]
  [Algebra K L] [Algebra R L] [IsScalarTower R A L] [IsScalarTower R K L]

open GenericCoefficientDescent

private theorem generic_factor
    (φ : (M.baseChange A L).Hom (N.baseChange A L)
      ((GroupScheme.baseChange (Spec.algebraMap K L)).map f)) :
    pullback.fst (M.baseChange A L).group.X.hom (Spec.algebraMap A L) ≫
        φ.hom.hom.hom.left ≫ pullback.fst N.group.X.hom (Spec.algebraMap R A) =
      (M.baseChange A L).genericIso.hom.hom.hom.left ≫
        pullback.fst G.X.hom (Spec.algebraMap K L) ≫ f.hom.hom.left ≫
          N.genericIso.inv.hom.hom.left ≫
            pullback.fst N.group.X.hom (Spec.algebraMap R K) := by
  have h := congrArg
    (fun g => g.hom.hom.left ≫ pullback.fst H.X.hom (Spec.algebraMap K L) ≫
      N.genericIso.inv.hom.hom.left ≫ pullback.fst N.group.X.hom (Spec.algebraMap R K))
    φ.generic_comm
  simp only [Grp.comp_hom_hom, Over.comp_left, Category.assoc] at h
  have hN := congrArg
    (fun g => ((GroupScheme.baseChange (Spec.algebraMap A L)).map φ.hom).hom.hom.left ≫ g)
    (N.baseChangeGenericIso_hom_fst A L)
  calc
    _ = ((GroupScheme.baseChange (Spec.algebraMap A L)).map φ.hom).hom.hom.left ≫
        pullback.fst (N.baseChange A L).group.X.hom (Spec.algebraMap A L) ≫
          pullback.fst N.group.X.hom (Spec.algebraMap R A) := by
      simpa only [Category.assoc] using
        (congrArg (fun g => g ≫ pullback.fst N.group.X.hom (Spec.algebraMap R A))
          (map_fst (Spec.algebraMap A L) φ.hom)).symm
    _ = ((GroupScheme.baseChange (Spec.algebraMap A L)).map φ.hom).hom.hom.left ≫
        (N.baseChangeGenericIso A L).hom.hom.hom.left ≫
          pullback.fst H.X.hom (Spec.algebraMap K L) ≫
            N.genericIso.inv.hom.hom.left ≫
              pullback.fst N.group.X.hom (Spec.algebraMap R K) := by
      change ((GroupScheme.baseChange (Spec.algebraMap A L)).map φ.hom).hom.hom.left ≫
        pullback.fst (pullback.snd N.group.X.hom (Spec.algebraMap R A))
          (Spec.algebraMap A L) ≫
        pullback.fst N.group.X.hom (Spec.algebraMap R A) = _
      simpa only [Category.assoc] using hN.symm
    _ = _ := h
    _ = _ := by rw [map_fst_assoc]

/-- An upstairs extension of the prescribed original generic morphism
automatically respects the canonical coefficient descent data. -/
theorem Hom.canonicalCompatible
    [Flat (Spec.algebraMap R A)]
    (φ : (M.baseChange A L).Hom (N.baseChange A L)
      ((GroupScheme.baseChange (Spec.algebraMap K L)).map f)) :
    Descent.Compatible (Descent.canonicalDatum (Spec.algebraMap R A) M.group)
      (Descent.canonicalDatum (Spec.algebraMap R A) N.group) φ.hom := by
  have : Flat (Spec.algebraMap A L) := by
    rw [Flat.SpecMap_iff, CommRingCat.hom_ofHom, RingHom.flat_algebraMap_iff]
    exact IsLocalization.flat L (nonZeroDivisors A)
  have : IsPreimmersion (Spec.algebraMap R K) :=
    IsPreimmersion.of_isLocalization (nonZeroDivisors R)
  have : IsSchemeTheoreticallyDominant
      (pullback.fst (M.baseChange A L).group.X.hom (Spec.algebraMap A L)) :=
    generic_projection_dominant A L _
  apply compatible_of_relation
  apply relation_eq_of_generic_factor
    (pullback.fst M.group.X.hom (Spec.algebraMap R A))
    (pullback.fst (M.baseChange A L).group.X.hom (Spec.algebraMap A L))
    M.group.X.hom N.group.X.hom
    (φ.hom.hom.hom.left ≫ pullback.fst N.group.X.hom (Spec.algebraMap R A))
    (by
      rw [Category.assoc, pullback.condition, ← Category.assoc]
      exact (congrArg (fun g => g ≫ Spec.algebraMap R A)
        (Over.w φ.hom.hom.hom)).trans pullback.condition.symm)
    (pullback.fst M.group.X.hom (Spec.algebraMap R K))
    ((M.baseChange A L).genericIso.hom.hom.hom.left ≫
      pullback.fst G.X.hom (Spec.algebraMap K L) ≫ M.genericIso.inv.hom.hom.left)
    (M.genericIso.hom.hom.hom.left ≫ f.hom.hom.left ≫
      N.genericIso.inv.hom.hom.left ≫
        pullback.fst N.group.X.hom (Spec.algebraMap R K))
  · exact M.baseChangeGenericIso_hom_fst A L
  · have hi : M.genericIso.inv.hom.hom.left ≫ M.genericIso.hom.hom.hom.left = 𝟙 _ :=
      congrArg (fun g => g.hom.hom.left) M.genericIso.inv_hom_id
    simpa only [Category.assoc, reassoc_of% hi, Category.id_comp] using
      generic_factor A L φ

variable [Flat (Spec.algebraMap R A)] [Surjective (Spec.algebraMap R A)]

/-- Descend an upstairs extension of the original generic map without an
additional Čech compatibility hypothesis. -/
def Hom.descendFromCoefficients
    (φ : (M.baseChange A L).Hom (N.baseChange A L)
      ((GroupScheme.baseChange (Spec.algebraMap K L)).map f)) : M.Hom N f :=
  φ.descendCoefficients A L (φ.canonicalCompatible A L)

/-- The descended morphism recovers the actual supplied upstairs map. -/
theorem Hom.baseChange_descendFromCoefficients
    (φ : (M.baseChange A L).Hom (N.baseChange A L)
      ((GroupScheme.baseChange (Spec.algebraMap K L)).map f)) :
    ((φ.descendFromCoefficients A L).baseChangeCoefficients A L).hom = φ.hom :=
  φ.baseChange_descendCoefficients A L (φ.canonicalCompatible A L)

/-- The descended extension is the unique one recovering the supplied map. -/
theorem Hom.descendFromCoefficients_unique
    (φ : (M.baseChange A L).Hom (N.baseChange A L)
      ((GroupScheme.baseChange (Spec.algebraMap K L)).map f))
    (ψ : M.Hom N f) (hψ : (ψ.baseChangeCoefficients A L).hom = φ.hom) :
    ψ = φ.descendFromCoefficients A L :=
  φ.descendCoefficients_unique A L (φ.canonicalCompatible A L) ψ hψ

private theorem hom_ext {a b : M.Hom N f} (h : a.hom = b.hom) : a = b := by
  cases a
  cases b
  cases h
  rfl

/-- Extending the prescribed generic map is invariant under this fpqc
coefficient extension, on the actual morphism types. -/
def Hom.coefficientEquiv :
    M.Hom N f ≃ (M.baseChange A L).Hom (N.baseChange A L)
      ((GroupScheme.baseChange (Spec.algebraMap K L)).map f) where
  toFun φ := φ.baseChangeCoefficients A L
  invFun φ := φ.descendFromCoefficients A L
  left_inv φ :=
    ((φ.baseChangeCoefficients A L).descendFromCoefficients_unique A L φ rfl).symm
  right_inv φ := hom_ext (φ.baseChange_descendFromCoefficients A L)

variable {f : G ≅ H}

/-- Descend an upstairs extending isomorphism using automatic canonical
compatibility of its actual forward map. -/
def Iso.descendFromCoefficients
    (e : (M.baseChange A L).Iso (N.baseChange A L)
      ((GroupScheme.baseChange (Spec.algebraMap K L)).mapIso f)) : M.Iso N f :=
  e.descendCoefficients A L (e.toHom.canonicalCompatible A L)

/-- The actual descended isomorphism pulls back to the supplied isomorphism. -/
theorem Iso.baseChange_descendFromCoefficients
    (e : (M.baseChange A L).Iso (N.baseChange A L)
      ((GroupScheme.baseChange (Spec.algebraMap K L)).mapIso f)) :
    (GroupScheme.baseChange (Spec.algebraMap R A)).mapIso
      (e.descendFromCoefficients A L).iso = e.iso :=
  e.baseChange_descendCoefficients A L (e.toHom.canonicalCompatible A L)

/-- An upstairs generic-identity model comparison identifies the original
downstairs integral-point images. -/
theorem integralPoints_eq_of_coefficientIso {N' : IntegralModel R K G}
    (e : (M.baseChange A L).Iso (N'.baseChange A L)
      ((GroupScheme.baseChange (Spec.algebraMap K L)).mapIso
        (CategoryTheory.Iso.refl G))) :
    M.integralPoints = N'.integralPoints :=
  (e.descendFromCoefficients A L).integralPoints_eq

end Coefficients

end Langlands.GroupScheme.IntegralModel
