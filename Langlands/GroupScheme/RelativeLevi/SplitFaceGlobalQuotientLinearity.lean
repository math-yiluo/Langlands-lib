import Langlands.GroupScheme.RelativeLevi.SplitFaceOriginalQuotientLinearity
import Langlands.GroupScheme.RelativeLevi.SplitFaceQuotientBaseChange
import Langlands.GroupScheme.SubgroupFunctor.EtaleLocality
import Langlands.GroupScheme.Reductive.FibrewiseRootDatumBaseChange
import Langlands.GroupScheme.Torus.FibrewiseMaximalBaseChange

/-! # Unconditional linearity of original canonical face quotient comparisons -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open CategoryTheory.Limits
open scoped CategoryTheory.MonObj Matrix

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.AutomorphicAction

variable {S : Scheme.{u}} {H U U' V V' : GroupScheme S}

/-- Equivariance transfers back through an actual equivariant isomorphism square. -/
theorem isEquivariant_of_iso_square
    (a : AutomorphicAction H U) (a' : AutomorphicAction H U')
    (b : AutomorphicAction H V) (b' : AutomorphicAction H V')
    (c : U ≅ V) (d : U' ≅ V') (φ : U ⟶ U') (ψ : V ⟶ V')
    (hc : a.IsEquivariant b c.hom) (hd : a'.IsEquivariant b' d.hom)
    (hψ : b.IsEquivariant b' ψ) (hs : c.hom ≫ ψ = φ ≫ d.hom) :
    a.IsEquivariant a' φ := by
  have hf : c.hom.hom.hom ≫ ψ.hom.hom = φ.hom.hom ≫ d.hom.hom.hom :=
    congrArg (fun f => f.hom.hom) hs
  intro T s x
  apply (cancel_mono d.hom.hom.hom).mp
  rw [Category.assoc, ← hf, ← Category.assoc, hc, hψ, hd,
    Category.assoc, hf, ← Category.assoc]

end Langlands.GroupScheme.AutomorphicAction

namespace Langlands.GroupScheme.VectorGroup

variable {R A : CommRingCat.{u}} {n m : ℕ}

/-- Actual coefficient extension of a vector morphism in canonical standard coordinates. -/
def coefficientMap (ρ : R ⟶ A) (φ : groupScheme R n ⟶ groupScheme R m) :
    groupScheme A n ⟶ groupScheme A m :=
  (baseChangeIso ρ).inv ≫ (GroupScheme.baseChange (Spec.map ρ)).map φ ≫
    (baseChangeIso ρ).hom

/-- The coefficient-map square retains the original actual pulled-back morphism. -/
theorem coefficientMap_fac (ρ : R ⟶ A) (φ : groupScheme R n ⟶ groupScheme R m) :
    (baseChangeIso ρ).hom ≫ coefficientMap ρ φ =
      (GroupScheme.baseChange (Spec.map ρ)).map φ ≫ (baseChangeIso ρ).hom := by
  simp only [coefficientMap, Iso.hom_inv_id_assoc]

/-- Equivariance in standard coefficient coordinates gives equivariance of the actual pullback map. -/
theorem pullback_isEquivariant_of_coefficientMap (ρ : R ⟶ A)
    (φ : groupScheme R n ⟶ groupScheme R m) (N : ℕ)
    (h : (powerWeightAction n N).IsEquivariant (powerWeightAction m N) (coefficientMap ρ φ)) :
    ((powerWeightAction n N).coefficientChange (Spec.map ρ)).IsEquivariant
      ((powerWeightAction m N).coefficientChange (Spec.map ρ))
      ((GroupScheme.baseChange (Spec.map ρ)).map φ) := by
  intro T s x
  exact AutomorphicAction.isEquivariant_of_iso_square _ _ _ _
    (baseChangeIso ρ) (baseChangeIso ρ) _ (coefficientMap ρ φ)
    (baseChangeIso_isEquivariant_power ρ N) (baseChangeIso_isEquivariant_power ρ N)
    h (coefficientMap_fac ρ φ) s x

/-- The same comparison along an arbitrary affine projection, retaining its exact pullback. -/
theorem pullback_isEquivariant_of_coefficientMap_affine (b : Spec A ⟶ Spec R)
    (φ : groupScheme R n ⟶ groupScheme R m) (N : ℕ)
    (h : (powerWeightAction n N).IsEquivariant (powerWeightAction m N)
      (coefficientMap (Spec.preimage b) φ)) :
    ((powerWeightAction n N).coefficientChange b).IsEquivariant
      ((powerWeightAction m N).coefficientChange b) ((GroupScheme.baseChange b).map φ) := by
  let P (c : Spec A ⟶ Spec R) : Prop :=
    ((powerWeightAction n N).coefficientChange c).IsEquivariant
      ((powerWeightAction m N).coefficientChange c) ((GroupScheme.baseChange c).map φ)
  have hp : P (Spec.map (Spec.preimage b)) := by
    intro T s x
    exact pullback_isEquivariant_of_coefficientMap (Spec.preimage b) φ N h s x
  intro T s x
  exact (Eq.mp (congrArg P (Spec.map_preimage b)) hp) s x

end Langlands.GroupScheme.VectorGroup

namespace Langlands.GroupScheme.FppfQuotientComparison

variable {R A : CommRingCat.{u}} {U V : GroupScheme (Spec R)} {n m : ℕ}

/-- Actual coefficient extension of a commuting vector-quotient square remains commuting. -/
theorem coefficientQuotient_fac (ρ : R ⟶ A)
    (q : U ⟶ VectorGroup.groupScheme R n) (q' : V ⟶ VectorGroup.groupScheme R m)
    (e : U ⟶ V) (E : VectorGroup.groupScheme R n ⟶ VectorGroup.groupScheme R m)
    (h : q ≫ E = e ≫ q') :
    coefficientQuotient ρ q ≫ VectorGroup.coefficientMap ρ E =
      (GroupScheme.baseChange (Spec.map ρ)).map e ≫ coefficientQuotient ρ q' := by
  simp only [coefficientQuotient, Category.assoc]
  rw [VectorGroup.coefficientMap_fac, ← Category.assoc, ← Functor.map_comp,
    h, Functor.map_comp]
  simp only [Category.assoc]

end Langlands.GroupScheme.FppfQuotientComparison

namespace Langlands.GroupScheme.AutomorphicAction

variable {S : Scheme.{u}} {U V : GroupScheme S}

/-- Actual Gm-equivariance is reflected by any étale cover of the base. -/
theorem isEquivariant_of_etale_coefficientChange
    (cover : S.Cover.{u} (Scheme.precoverage @Etale))
    (a : AutomorphicAction (Gm S).toGrp U) (b : AutomorphicAction (Gm S).toGrp V)
    (φ : U ⟶ V)
    (h : ∀ k, (a.coefficientChange (cover.f k)).IsEquivariant
      (b.coefficientChange (cover.f k)) ((GroupScheme.baseChange (cover.f k)).map φ)) :
    a.IsEquivariant b φ := by
  intro T s x
  let : Scheme.IsJointlySurjectivePreserving (@Etale.{u}) :=
    Scheme.isJointlySurjectivePreserving _
  let cov := cover.pullback₁ T.hom
  let : EffectiveEpiFamily cov.X cov.f := SubgroupFunctor.effectiveEpiFamily_etaleCover cov
  apply Over.OverMorphism.ext
  apply EffectiveEpiFamily.hom_ext cov.X cov.f
  intro k
  let W : Over (cover.X k) := Over.mk (pullback.snd T.hom (cover.f k))
  let q : (Over.map (cover.f k)).obj W ⟶ T :=
    Over.homMk (pullback.fst T.hom (cover.f k)) pullback.condition
  let xs := (baseChangePointsEquiv (cover.f k) U W).symm (q ≫ x)
  let ss := (baseChangePointsEquiv (cover.f k) (Gm S).toGrp W).symm (q ≫ s) ≫
    (Gm.baseChangeIso (cover.f k)).hom.hom.hom
  have hs : baseChangePointsEquiv (cover.f k) (Gm S).toGrp W
      (ss ≫ (Gm.baseChangeIso (cover.f k)).inv.hom.hom) = q ≫ s := by
    simp only [ss, Category.assoc, iso_hom_inv_hom, Category.comp_id, MulEquiv.apply_symm_apply]
  have hx : baseChangePointsEquiv (cover.f k) U W xs = q ≫ x :=
    MulEquiv.apply_symm_apply _ _
  have he := congrArg (baseChangePointsEquiv (cover.f k) V W) (h k ss xs)
  rw [baseChangePointsEquiv_comp, coefficientChange_act, coefficientChange_act,
    baseChangePointsEquiv_comp, hs, hx] at he
  have he' : q ≫ (a.act s x ≫ φ.hom.hom) = q ≫ b.act s (x ≫ φ.hom.hom) := by
    rw [← Category.assoc, a.naturality, b.naturality, ← Category.assoc]
    exact he
  exact congrArg (fun f => f.left) he'

end Langlands.GroupScheme.AutomorphicAction

namespace Langlands.GroupScheme.SplitParabolicFaceChart

open LocalSplitCell LocalSplitRootBaseChange RelativeUnipotent

variable {R : Type u} [CommRing R] [Nontrivial R]
  {I I' J J' : Type u} [Fintype I] [Fintype I'] [Fintype J] [Fintype J']
  [DecidableEq I] [DecidableEq I']
  {G : GroupScheme (Spec (CommRingCat.of R))} [IsAffineHom G.X.hom]
  {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}
  {j : splitTorus (Spec (CommRingCat.of R)) I' ⟶ G}
  {P : RootDatum J (I → ℤ) (I → ℤ)} {Q : RootDatum J' (I' → ℤ) (I' → ℤ)}
  {fam : J → (Ga R ⟶ G)} {fam' : J' → (Ga R ⟶ G)}
  {wt : I → ℤ} {wt' : I' → ℤ}
  (C : SplitParabolicFaceChart i P fam wt) (D : SplitParabolicFaceChart j Q fam' wt')
  (hG : IsReductive G)
  (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
  (hmax' : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I') j)
  (hP : IsFibrewiseRootDatumOf I G i P) (hQ : IsFibrewiseRootDatumOf I' G j Q)
  (hfam : ∀ a, IsRootParametrization i (P.root a) (fam a))
  (hfam' : ∀ a, IsRootParametrization j (Q.root a) (fam' a))
  (hU : Dynamic.unipotent (AffineRegularBorel.cocharacter i wt) =
    Dynamic.unipotent (AffineRegularBorel.cocharacter j wt'))
  (hPar : Dynamic.parabolic (AffineRegularBorel.cocharacter i wt) =
    Dynamic.parabolic (AffineRegularBorel.cocharacter j wt'))

local instance globalLinearityAffine : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom

section CoefficientSquare

variable (A : Type u) [CommRing A] [Algebra R A] [Nontrivial A]

local instance coefficientAffineHom :
    IsAffineHom ((GroupScheme.baseChange (algebraBaseMap R A)).obj G).X.hom :=
  MorphismProperty.pullback_snd G.X.hom (algebraBaseMap R A) inferInstance

variable
  (CA : SplitParabolicFaceChart (splitTorus.baseChangeHom (K := A) G I i)
    P (fun a => baseChangeRoot A (fam a)) wt)
  (DA : SplitParabolicFaceChart (splitTorus.baseChangeHom (K := A) G I' j)
    Q (fun a => baseChangeRoot A (fam' a)) wt')
  (hUA : Dynamic.unipotent (AffineRegularBorel.cocharacter (splitTorus.baseChangeHom (K := A) G I i) wt) =
    Dynamic.unipotent (AffineRegularBorel.cocharacter (splitTorus.baseChangeHom (K := A) G I' j) wt'))
  (hParA : Dynamic.parabolic (AffineRegularBorel.cocharacter (splitTorus.baseChangeHom (K := A) G I i) wt) =
    Dynamic.parabolic (AffineRegularBorel.cocharacter (splitTorus.baseChangeHom (K := A) G I' j) wt'))

include hG hmax hmax' hP hQ hfam hfam' hU hPar in
/-- Actual original canonical term comparison commutes with independent fresh coefficient charts. -/
theorem sameParabolicTermIso_affineBaseChange_square (d : ℕ) :
    (GroupScheme.baseChange (algebraBaseMap R A)).map
        (C.sameParabolicTermIso D hG hmax hmax' hP hQ hfam hfam' hU hPar d).hom ≫
        (D.affineBaseChangeTermIso A DA hG hmax' hQ d).hom =
      (C.affineBaseChangeTermIso A CA hG hmax hP d).hom ≫
        (CA.sameParabolicTermIso DA (hG.baseChange _)
          (by have : Smooth G.X.hom := hG.smooth
              exact splitTorus.isFibrewiseMaximalTorus_coordinateBaseChange I G i _ hmax)
          (by have : Smooth G.X.hom := hG.smooth
              exact splitTorus.isFibrewiseMaximalTorus_coordinateBaseChange I' G j _ hmax')
          hP.baseChange_implicit hQ.baseChange_implicit
          (fun a => isRootParametrization_baseChangeRoot A i _ _ (hfam a))
          (fun a => isRootParametrization_baseChangeRoot A j _ _ (hfam' a)) hUA hParA d).hom := by
  let b := DA.weights.inclusion d ≫ Dynamic.Affine.unipotentHom
    (AffineRegularBorel.cocharacter (splitTorus.baseChangeHom (K := A) G I' j) DA.cocharacter)
  have : Mono b.hom.hom := by
    change Mono ((DA.weights.inclusion d).hom.hom ≫ _)
    exact mono_comp' (DA.weights.isRepresentedBy_inclusion d).1
      (Dynamic.Affine.isRepresentedBy_unipotentHom _).1
  have hb : (SubgroupFunctor.range b).IsRepresentedBy b := ⟨inferInstance, rfl⟩
  apply hb.hom_ext
  rw [Category.assoc, D.affineBaseChangeTermIso_hom_comp A DA hG hmax' hQ d,
    ← Functor.map_comp, C.sameParabolicTermIso_hom_comp D hG hmax hmax' hP hQ hfam hfam' hU hPar d]
  rw [Category.assoc, CA.sameParabolicTermIso_hom_comp,
    C.affineBaseChangeTermIso_hom_comp A CA hG hmax hP d]

include hG hmax hmax' hP hQ hfam hfam' hU hPar in
/-- The original actual quotient map, in standard coefficient coordinates, agrees with fresh comparison. -/
theorem sameParabolicQuotientIso_affineBaseChange_square (d : ℕ) :
    (C.affineBaseChangeQuotientIso A CA hG hmax hP d).hom ≫
        (CA.sameParabolicQuotientIso DA (hG.baseChange _)
          (by have : Smooth G.X.hom := hG.smooth
              exact splitTorus.isFibrewiseMaximalTorus_coordinateBaseChange I G i _ hmax)
          (by have : Smooth G.X.hom := hG.smooth
              exact splitTorus.isFibrewiseMaximalTorus_coordinateBaseChange I' G j _ hmax')
          hP.baseChange_implicit hQ.baseChange_implicit
          (fun a => isRootParametrization_baseChangeRoot A i _ _ (hfam a))
          (fun a => isRootParametrization_baseChangeRoot A j _ _ (hfam' a)) hUA hParA d).hom =
      VectorGroup.coefficientMap (CommRingCat.ofHom (algebraMap R A))
        (C.sameParabolicQuotientIso D hG hmax hmax' hP hQ hfam hfam' hU hPar d).hom ≫
        (D.affineBaseChangeQuotientIso A DA hG hmax' hQ d).hom := by
  apply FppfQuotientComparison.hom_ext (C.isFppfQuotient_affineBaseChangeQuotientMap A d)
  rw [← Category.assoc, C.affineBaseChangeQuotientIso_fac A CA hG hmax hP d,
    Category.assoc, CA.quotientMap_comp_sameParabolicQuotientIso]
  have hcoef : C.affineBaseChangeQuotientMap A d ≫
      VectorGroup.coefficientMap (CommRingCat.ofHom (algebraMap R A))
        (C.sameParabolicQuotientIso D hG hmax hmax' hP hQ hfam hfam' hU hPar d).hom =
      (GroupScheme.baseChange (algebraBaseMap R A)).map
        (C.sameParabolicTermIso D hG hmax hmax' hP hQ hfam hfam' hU hPar d).hom ≫
          D.affineBaseChangeQuotientMap A d :=
    FppfQuotientComparison.coefficientQuotient_fac _
      (C.weights.quotientMap d) (D.weights.quotientMap d) _ _
      (C.quotientMap_comp_sameParabolicQuotientIso D hG hmax hmax' hP hQ hfam hfam' hU hPar d)
  rw [← Category.assoc (C.affineBaseChangeQuotientMap A d), hcoef, Category.assoc,
    D.affineBaseChangeQuotientIso_fac A DA hG hmax' hQ d]
  simpa only [Category.assoc] using congrArg (fun f => f ≫ DA.weights.quotientMap d)
    (C.sameParabolicTermIso_affineBaseChange_square D hG hmax hmax' hP hQ hfam hfam'
      hU hPar A CA DA hUA hParA d).symm

include hG hmax hmax' hP hQ hfam hfam' hU hPar CA DA hUA hParA in
/-- On an actual coefficient neighborhood with a parabolic coordinate conjugator,
the ORIGINAL coefficient map commutes with every common scalar power. -/
theorem coefficientMap_sameParabolicQuotientIso_isEquivariant
    (E : (I → ℤ) ≃ₗ[ℤ] (I' → ℤ))
    (g : Over.mk (𝟙 (Spec (CommRingCat.of A))) ⟶
      ((GroupScheme.baseChange (algebraBaseMap R A)).obj G).X)
    (hg : g ∈ (Dynamic.parabolic (AffineRegularBorel.cocharacter
      (splitTorus.baseChangeHom (K := A) G I i) wt)).carrier _)
    (hsquare : splitTorus.baseChangeHom (K := A) G I i ≫
        (((GroupScheme.baseChange (algebraBaseMap R A)).obj G).innerIso g).hom =
      precompTorus E (splitTorus.baseChangeHom (K := A) G I' j)) (d N : ℕ) :
    (VectorGroup.powerWeightAction (Nat.card (C.weights.exactSupport d)) N).IsEquivariant
      (VectorGroup.powerWeightAction (Nat.card (D.weights.exactSupport d)) N)
      (VectorGroup.coefficientMap (CommRingCat.ofHom (algebraMap R A))
        (C.sameParabolicQuotientIso D hG hmax hmax' hP hQ hfam hfam' hU hPar d).hom) := by
  have : Smooth G.X.hom := hG.smooth
  have hm := splitTorus.isFibrewiseMaximalTorus_coordinateBaseChange
    I G i (algebraBaseMap R A) hmax
  have hm' := splitTorus.isFibrewiseMaximalTorus_coordinateBaseChange
    I' G j (algebraBaseMap R A) hmax'
  have hpA : IsFibrewiseRootDatumOf I ((GroupScheme.baseChange (algebraBaseMap R A)).obj G)
      (splitTorus.baseChangeHom (K := A) G I i) P := hP.baseChange_implicit
  have hqA : IsFibrewiseRootDatumOf I' ((GroupScheme.baseChange (algebraBaseMap R A)).obj G)
      (splitTorus.baseChangeHom (K := A) G I' j) Q := hQ.baseChange_implicit
  let hfA := fun a => isRootParametrization_baseChangeRoot A i (P.root a) (fam a) (hfam a)
  let hfA' := fun a => isRootParametrization_baseChangeRoot A j (Q.root a) (fam' a) (hfam' a)
  rw [← (Dynamic.Affine.isRepresentedBy_parabolicHom
    (AffineRegularBorel.cocharacter (splitTorus.baseChangeHom (K := A) G I i) wt)).2] at hg
  obtain ⟨u, hu⟩ := SubgroupFunctor.mem_range.mp hg
  have hs : splitTorus.baseChangeHom (K := A) G I i ≫
      (((GroupScheme.baseChange (algebraBaseMap R A)).obj G).innerIso
        (u ≫ (AffineRegularBorel.inclusion (splitTorus.baseChangeHom (K := A) G I i) wt).hom.hom)).hom =
      precompTorus E (splitTorus.baseChangeHom (K := A) G I' j) := by
    rw [hu]
    exact hsquare
  have hfresh : (VectorGroup.powerWeightAction (Nat.card (CA.weights.exactSupport d)) N).IsEquivariant
      (VectorGroup.powerWeightAction (Nat.card (DA.weights.exactSupport d)) N)
      (CA.sameParabolicQuotientIso DA (hG.baseChange _) hm hm' hpA hqA hfA hfA' hUA hParA d).hom := by
    apply VectorGroup.isEquivariant_power_of_hasScalarWeight _
      (Nat.mul_pos CA.faceMultiplier_pos (Nat.succ_pos d))
    exact CA.sameParabolicQuotientIso_hasScalarWeight_of_coordinateConjugacy DA
      (hG.baseChange _) hm hm' hpA hqA hfA hfA' hUA hParA E u hs d
  intro T s x
  exact AutomorphicAction.isEquivariant_of_iso_square _ _ _ _
    (C.affineBaseChangeQuotientIso A CA hG hmax hP d)
    (D.affineBaseChangeQuotientIso A DA hG hmax' hQ d) _ _
    (C.affineBaseChangeQuotientIso_isEquivariant_power A CA hG hmax hP hfam d N)
    (D.affineBaseChangeQuotientIso_isEquivariant_power A DA hG hmax' hQ hfam' d N)
    hfresh (C.sameParabolicQuotientIso_affineBaseChange_square D hG hmax hmax' hP hQ
      hfam hfam' hU hPar A CA DA hUA hParA d) s x

end CoefficientSquare

section DerivedCoefficientGeometry

variable (A : Type u) [CommRing A] [Algebra R A] [Nontrivial A]

local instance derivedCoefficientAffineHom :
    IsAffineHom ((GroupScheme.baseChange (algebraBaseMap R A)).obj G).X.hom :=
  MorphismProperty.pullback_snd G.X.hom (algebraBaseMap R A) inferInstance

include hG hmax hmax' hP hQ hfam hfam' hU hPar in
/-- Every geometric coefficient input is derived for an actual coordinate-conjugacy neighborhood. -/
theorem coefficientMap_sameParabolicQuotientIso_isEquivariant_of_conjugacy
    (E : (I → ℤ) ≃ₗ[ℤ] (I' → ℤ))
    (g : Over.mk (𝟙 (Spec (CommRingCat.of A))) ⟶
      ((GroupScheme.baseChange (algebraBaseMap R A)).obj G).X)
    (hg : g ∈ ((Dynamic.parabolic (AffineRegularBorel.cocharacter i wt)).baseChange
      (algebraBaseMap R A)).carrier _)
    (hsquare : splitTorus.baseChangeHom (K := A) G I i ≫
        (((GroupScheme.baseChange (algebraBaseMap R A)).obj G).innerIso g).hom =
      precompTorus E (splitTorus.baseChangeHom (K := A) G I' j)) (d N : ℕ) :
    (VectorGroup.powerWeightAction (Nat.card (C.weights.exactSupport d)) N).IsEquivariant
      (VectorGroup.powerWeightAction (Nat.card (D.weights.exactSupport d)) N)
      (VectorGroup.coefficientMap (CommRingCat.ofHom (algebraMap R A))
        (C.sameParabolicQuotientIso D hG hmax hmax' hP hQ hfam hfam' hU hPar d).hom) := by
  let b := algebraBaseMap R A
  let GA := (GroupScheme.baseChange b).obj G
  let iA := splitTorus.baseChangeHom (K := A) G I i
  let jA := splitTorus.baseChangeHom (K := A) G I' j
  have hGA : IsReductive GA := hG.baseChange b
  have : Smooth G.X.hom := hG.smooth
  have hm : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) iA :=
    splitTorus.isFibrewiseMaximalTorus_coordinateBaseChange I G i b hmax
  have hm' : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I') jA :=
    splitTorus.isFibrewiseMaximalTorus_coordinateBaseChange I' G j b hmax'
  have hpA : IsFibrewiseRootDatumOf I GA iA P := hP.baseChange_implicit
  have hqA : IsFibrewiseRootDatumOf I' GA jA Q := hQ.baseChange_implicit
  let hfA := fun a => isRootParametrization_baseChangeRoot A i (P.root a) (fam a) (hfam a)
  let hfA' := fun a => isRootParametrization_baseChangeRoot A j (Q.root a) (fam' a) (hfam' a)
  let CA : SplitParabolicFaceChart iA P (fun a => baseChangeRoot A (fam a)) wt :=
    Classical.choice (nonempty_splitParabolicFaceChart hGA hm hpA hfA)
  let DA : SplitParabolicFaceChart jA Q (fun a => baseChangeRoot A (fam' a)) wt' :=
    Classical.choice (nonempty_splitParabolicFaceChart hGA hm' hqA hfA')
  have hc : Dynamic.baseChangeCocharacter b (AffineRegularBorel.cocharacter i wt) =
      AffineRegularBorel.cocharacter iA wt :=
    splitTorus.RelativeCocharacterCentralizer.cocharacter_baseChange I G i wt b
  have hc' : Dynamic.baseChangeCocharacter b (AffineRegularBorel.cocharacter j wt') =
      AffineRegularBorel.cocharacter jA wt' :=
    splitTorus.RelativeCocharacterCentralizer.cocharacter_baseChange I' G j wt' b
  have hUA : Dynamic.unipotent (AffineRegularBorel.cocharacter iA wt) =
      Dynamic.unipotent (AffineRegularBorel.cocharacter jA wt') := by
    rw [← hc, ← hc', Dynamic.unipotent_baseChange, Dynamic.unipotent_baseChange, hU]
  have hParA : Dynamic.parabolic (AffineRegularBorel.cocharacter iA wt) =
      Dynamic.parabolic (AffineRegularBorel.cocharacter jA wt') := by
    rw [← hc, ← hc', Dynamic.parabolic_baseChange, Dynamic.parabolic_baseChange, hPar]
  have hgA : g ∈ (Dynamic.parabolic (AffineRegularBorel.cocharacter iA wt)).carrier _ := by
    rw [← hc, Dynamic.parabolic_baseChange]
    exact hg
  intro T s x
  exact C.coefficientMap_sameParabolicQuotientIso_isEquivariant D
    hG hmax hmax' hP hQ hfam hfam' hU hPar A CA DA hUA hParA E g hgA hsquare d N s x

end DerivedCoefficientGeometry

include hG hmax hmax' hP hQ hfam hfam' hU hPar in
/-- The actual neighborhood may use any specified affine projection to the original base. -/
theorem coefficientMap_sameParabolicQuotientIso_isEquivariant_of_affine_conjugacy
    (A : CommRingCat.{u}) [Nontrivial A] (b : Spec A ⟶ Spec (CommRingCat.of R))
    (E : (I → ℤ) ≃ₗ[ℤ] (I' → ℤ))
    (g : Over.mk (𝟙 (Spec A)) ⟶ ((GroupScheme.baseChange b).obj G).X)
    (hg : g ∈ ((Dynamic.parabolic (AffineRegularBorel.cocharacter i wt)).baseChange b).carrier _)
    (hsquare : ((splitTorus.baseChangeIso b I).inv ≫ (GroupScheme.baseChange b).map i) ≫
        (((GroupScheme.baseChange b).obj G).innerIso g).hom =
      CommGroupScheme.groupHom (splitTorus.exponentEquivIso (Spec A) E).hom ≫
        ((splitTorus.baseChangeIso b I').inv ≫ (GroupScheme.baseChange b).map j)) (d N : ℕ) :
    (VectorGroup.powerWeightAction (Nat.card (C.weights.exactSupport d)) N).IsEquivariant
      (VectorGroup.powerWeightAction (Nat.card (D.weights.exactSupport d)) N)
      (VectorGroup.coefficientMap (Spec.preimage b)
        (C.sameParabolicQuotientIso D hG hmax hmax' hP hQ hfam hfam' hU hPar d).hom) := by
  let : Algebra R A := (Spec.preimage b).hom.toAlgebra
  have hb : algebraBaseMap R A = b := Spec.map_preimage b
  let F (b : Spec A ⟶ Spec (CommRingCat.of R)) : Prop :=
    ∀ (E : (I → ℤ) ≃ₗ[ℤ] (I' → ℤ))
      (g : Over.mk (𝟙 (Spec A)) ⟶ ((GroupScheme.baseChange b).obj G).X),
      g ∈ ((Dynamic.parabolic (AffineRegularBorel.cocharacter i wt)).baseChange b).carrier _ →
      (((splitTorus.baseChangeIso b I).inv ≫ (GroupScheme.baseChange b).map i) ≫
          (((GroupScheme.baseChange b).obj G).innerIso g).hom =
        CommGroupScheme.groupHom (splitTorus.exponentEquivIso (Spec A) E).hom ≫
          ((splitTorus.baseChangeIso b I').inv ≫ (GroupScheme.baseChange b).map j)) →
      (VectorGroup.powerWeightAction (Nat.card (C.weights.exactSupport d)) N).IsEquivariant
        (VectorGroup.powerWeightAction (Nat.card (D.weights.exactSupport d)) N)
        (VectorGroup.coefficientMap (Spec.preimage b)
          (C.sameParabolicQuotientIso D hG hmax hmax' hP hQ hfam hfam' hU hPar d).hom)
  have h : F (algebraBaseMap R A) := by
    intro E g hg hs T s x
    have hh := C.coefficientMap_sameParabolicQuotientIso_isEquivariant_of_conjugacy D
      hG hmax hmax' hP hQ hfam hfam' hU hPar A E g hg hs d N s x
    simpa only [algebraBaseMap, Spec.preimage_map] using hh
  intro T s x
  exact (Eq.mp (congrArg F hb) h) E g hg hsquare s x

include hG hmax hmax' hP hQ hfam hfam' hU hPar in
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The original canonical quotient comparison commutes with every scalar power,
without a supplied coordinate conjugator or local linearity premise. -/
theorem sameParabolicQuotientIso_isEquivariant_power (d N : ℕ) :
    (VectorGroup.powerWeightAction (Nat.card (C.weights.exactSupport d)) N).IsEquivariant
      (VectorGroup.powerWeightAction (Nat.card (D.weights.exactSupport d)) N)
      (C.sameParabolicQuotientIso D hG hmax hmax' hP hQ hfam hfam' hU hPar d).hom := by
  have : Smooth G.X.hom := hG.smooth
  let L (s : Spec (CommRingCat.of R)) :=
    splitTorus.etaleParabolicCoordinateConjugacyAt G i j wt wt' hmax hmax' hPar s
  let cover : (Spec (CommRingCat.of R)).Cover.{u} (Scheme.precoverage @Etale) :=
    Scheme.Cover.mkOfCovers (P := @Etale) (Spec (CommRingCat.of R))
      (fun s => Spec (L s).ring) (fun s => (L s).projection)
      (fun s => ⟨s, (L s).mem_range.choose, (L s).mem_range.choose_spec⟩)
      (fun s => (L s).etale)
  apply AutomorphicAction.isEquivariant_of_etale_coefficientChange cover
  intro s
  let : Nontrivial (L s).ring := (L s).mem_range.choose.nontrivial
  have hlocal :
      (VectorGroup.powerWeightAction (R := (L s).ring) (Nat.card (C.weights.exactSupport d)) N).IsEquivariant
        (VectorGroup.powerWeightAction (Nat.card (D.weights.exactSupport d)) N)
        (VectorGroup.coefficientMap (Spec.preimage (L s).projection)
          (C.sameParabolicQuotientIso D hG hmax hmax' hP hQ hfam hfam' hU hPar d).hom) := by
    intro T t x
    exact C.coefficientMap_sameParabolicQuotientIso_isEquivariant_of_affine_conjugacy D
      hG hmax hmax' hP hQ hfam hfam' hU hPar (L s).ring (L s).projection
      (L s).coordinateMap (L s).conjugator (L s).mem_parabolic (L s).square d N t x
  intro T t x
  exact VectorGroup.pullback_isEquivariant_of_coefficientMap_affine (L s).projection
    (C.sameParabolicQuotientIso D hG hmax hmax' hP hQ hfam hfam' hU hPar d).hom N hlocal t x

include hG hmax hmax' hP hQ hfam hfam' hU hPar in
/-- Unconditional scalar weight one for the actual original canonical comparison. -/
theorem sameParabolicQuotientIso_hasScalarWeight (d : ℕ) :
    VectorGroup.HasScalarWeight (VectorGroup.pointTransformation
      (C.sameParabolicQuotientIso D hG hmax hmax' hP hQ hfam hfam' hU hPar d).hom) 1 :=
  VectorGroup.hasScalarWeight_of_equivariant _ _
    (C.sameParabolicQuotientIso_isEquivariant_power D
      hG hmax hmax' hP hQ hfam hfam' hU hPar d 1)

/-- The actual original canonical quotient comparison is linear over every coefficient algebra. -/
def sameParabolicLayerLinearEquiv (d : ℕ) (A : CommAlgCat.{u} (CommRingCat.of R)) :
    (Fin (Nat.card (C.weights.exactSupport d)) → A) ≃ₗ[A]
      (Fin (Nat.card (D.weights.exactSupport d)) → A) :=
  VectorGroup.linearEquivOfWeight
    (C.sameParabolicQuotientIso D hG hmax hmax' hP hQ hfam hfam' hU hPar d)
    (by decide : 0 < 1)
    (C.sameParabolicQuotientIso_hasScalarWeight D
      hG hmax hmax' hP hQ hfam hfam' hU hPar d) A

include hG hmax hmax' hP hQ hfam hfam' hU hPar in
/-- One base-ring matrix describes the actual original comparison on all tests. -/
theorem sameParabolicQuotientIso_eq_matrixHom (d : ℕ) :
    (C.sameParabolicQuotientIso D hG hmax hmax' hP hQ hfam hfam' hU hPar d).hom =
      VectorGroup.matrixHom (VectorGroup.weightMatrix (VectorGroup.pointTransformation
        (C.sameParabolicQuotientIso D hG hmax hmax' hP hQ hfam hfam' hU hPar d).hom)) :=
  VectorGroup.eq_matrixHom_of_hasScalarWeight _ (by decide : 0 < 1)
    (C.sameParabolicQuotientIso_hasScalarWeight D
      hG hmax hmax' hP hQ hfam hfam' hU hPar d)

include hG hmax hmax' hP hQ hfam hfam' hU hPar in
/-- The matrix formula applies to the ORIGINAL quotient morphism on every scheme test. -/
theorem coordinates_sameParabolicQuotientIso (d : ℕ)
    (T : Over (Spec (CommRingCat.of R)))
    (x : T ⟶ (VectorGroup.groupScheme (CommRingCat.of R)
      (Nat.card (C.weights.exactSupport d))).X) :
    (VectorGroup.coordinates (CommRingCat.of R) (Nat.card (D.weights.exactSupport d)) T
      (x ≫ (C.sameParabolicQuotientIso D hG hmax hmax' hP hQ hfam hfam' hU hPar d).hom.hom.hom)).toAdd =
      (VectorGroup.weightMatrix (VectorGroup.pointTransformation
        (C.sameParabolicQuotientIso D hG hmax hmax' hP hQ hfam hfam' hU hPar d).hom)).map
          (scalarMap T) *ᵥ
      (VectorGroup.coordinates (CommRingCat.of R) (Nat.card (C.weights.exactSupport d)) T x).toAdd :=
  VectorGroup.coordinates_of_hasScalarWeight _ (by decide : 0 < 1)
    (C.sameParabolicQuotientIso_hasScalarWeight D
      hG hmax hmax' hP hQ hfam hfam' hU hPar d) T x

end Langlands.GroupScheme.SplitParabolicFaceChart
