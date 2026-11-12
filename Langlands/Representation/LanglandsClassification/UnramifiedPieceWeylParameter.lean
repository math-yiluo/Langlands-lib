import Langlands.Representation.LanglandsClassification.UnramifiedFullParameter
import Langlands.Representation.Exponents.TemperedTwistedGeometricPieceCone
import Langlands.Representation.Geometric.RepresentedGeometricLemmaCommonTorus
import Langlands.GroupScheme.Rational.MaximalSplitTorusConjugacyProof
import Langlands.GroupScheme.Rational.CentralTorusFixedness

/-! # The actual Weyl parameter of an unramified geometric-lemma piece -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {G M : GroupScheme (Spec (CommRingCat.of k))}
  {T S : CommGroupScheme (Spec (CommRingCat.of k))}

/-- Two occurrences of a common ambient maximal split torus inside one
connected reductive subgroup correct their conjugating point to a normalizer
representative by left and right multiplication inside that subgroup. -/
theorem exists_normalizerPoint_of_commonSplitTorus
    (hM : IsConnectedReductive M) (j : M ⟶ G) (hj : IsClosedSubgroup j)
    (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i)
    (iM : T.toGrp ⟶ M) (hiM : iM ≫ j = i)
    (s t : S.toGrp ⟶ M)
    (hs : IsMaximalSplitTorus (s ≫ j)) (ht : IsMaximalSplitTorus (t ≫ j))
    (z : rationalPoints G) (hst : s ≫ j = t ≫ j ≫ (G.innerIso z).hom) :
    ∃ (mS mT : rationalPoints M) (n : normalizerPoints i),
      n.val = (mS ≫ j.hom.hom) * z * (mT ≫ j.hom.hom)⁻¹ := by
  have hiM' : IsMaximalSplitTorus iM :=
    IsMaximalSplitTorus.of_comp hj (hiM.symm ▸ hi)
  have hsM : IsMaximalSplitTorus s := IsMaximalSplitTorus.of_comp hj hs
  have htM : IsMaximalSplitTorus t := IsMaximalSplitTorus.of_comp hj ht
  obtain ⟨mS, eS, heS⟩ := (maximalSplitTorusConjugacy k M hM).1 S T s iM hsM hiM'
  obtain ⟨mT, eT, heT⟩ := (maximalSplitTorusConjugacy k M hM).1 S T t iM htM hiM'
  have heS' : (s ≫ j) ≫ (G.innerIso (mS ≫ j.hom.hom)).hom = eS.hom ≫ i := by
    rw [Category.assoc, ← innerIso_hom_comp, ← Category.assoc, heS,
      Category.assoc, hiM]
  have heT' : (t ≫ j) ≫ (G.innerIso (mT ≫ j.hom.hom)).hom = eT.hom ≫ i := by
    rw [Category.assoc, ← innerIso_hom_comp, ← Category.assoc, heT,
      Category.assoc, hiM]
  have heTinv : i ≫ (G.innerIso (mT ≫ j.hom.hom)⁻¹).hom = eT.inv ≫ (t ≫ j) := by
    rw [innerIso_inv_hom, Iso.comp_inv_eq, Category.assoc, heT',
      Iso.inv_hom_id_assoc]
  let e : T.toGrp ≅ T.toGrp := eT.symm ≪≫ eS
  let σ : T ≅ T :=
    { hom := Additive.ofMul e.hom
      inv := Additive.ofMul e.inv
      hom_inv_id := congrArg Additive.ofMul e.hom_inv_id
      inv_hom_id := congrArg Additive.ofMul e.inv_hom_id }
  have hn : IsNormalizingPoint i
      ((mS ≫ j.hom.hom) * z * (mT ≫ j.hom.hom)⁻¹) σ := by
    change i ≫ (G.innerIso
      ((mS ≫ j.hom.hom) * z * (mT ≫ j.hom.hom)⁻¹)).hom =
        (eT.inv ≫ eS.hom) ≫ i
    calc
      _ = (i ≫ (G.innerIso (mT ≫ j.hom.hom)⁻¹).hom) ≫
          (G.innerIso z).hom ≫ (G.innerIso (mS ≫ j.hom.hom)).hom := by
        simp only [innerIso_mul_hom, Category.assoc]
      _ = eT.inv ≫ (t ≫ j ≫ (G.innerIso z).hom) ≫
          (G.innerIso (mS ≫ j.hom.hom)).hom := by
        rw [heTinv]
        simp only [Category.assoc]
      _ = eT.inv ≫ ((s ≫ j) ≫ (G.innerIso (mS ≫ j.hom.hom)).hom) := by
        rw [← hst]
      _ = (eT.inv ≫ eS.hom) ≫ i := by
        rw [heS', Category.assoc]
  exact ⟨mS, mT, ⟨_, ⟨σ, hn⟩⟩, rfl⟩

variable {A : CommGroupScheme (Spec (CommRingCat.of k))}

/-- For a central component, the original conjugated map differs from the
normalizer pullback only by an inner automorphism of the Levi. -/
theorem comp_innerIso_eq_normalizer_pullback
    (j : M ⟶ G) (hj : IsClosedSubgroup j)
    (i : T.toGrp ⟶ G) (iM : T.toGrp ⟶ M) (hiM : iM ≫ j = i)
    (a b : A.toGrp ⟶ M) (ha : IsCentral a)
    (f : A ⟶ T) (hf : CommGroupScheme.groupHom f ≫ iM = a)
    (z : rationalPoints G) (hb : b ≫ j = a ≫ j ≫ (G.innerIso z).hom)
    (mS mT : rationalPoints M) (n : normalizerPoints i)
    (hn : n.val = (mS ≫ j.hom.hom) * z * (mT ≫ j.hom.hom)⁻¹) :
    b ≫ (M.innerIso mS).hom =
      CommGroupScheme.groupHom (f ≫ (normalizingAut i n).hom) ≫ iM := by
  have hinv : (mT ≫ j.hom.hom)⁻¹ = mT⁻¹ ≫ j.hom.hom :=
    (map_inv (rationalPoints.map j) mT).symm
  have hc : a ≫ j ≫ (G.innerIso (mT ≫ j.hom.hom)⁻¹).hom = a ≫ j := by
    rw [hinv, ← innerIso_hom_comp, ← Category.assoc, ha.comp_innerIso_hom]
  have hconj : a ≫ j ≫ (G.innerIso n.val).hom =
      (b ≫ (M.innerIso mS).hom) ≫ j := by
    calc
      _ = (a ≫ j ≫ (G.innerIso (mT ≫ j.hom.hom)⁻¹).hom) ≫
          (G.innerIso z).hom ≫ (G.innerIso (mS ≫ j.hom.hom)).hom := by
        rw [hn]
        simp only [innerIso_mul_hom, Category.assoc]
      _ = (a ≫ j ≫ (G.innerIso z).hom) ≫
          (G.innerIso (mS ≫ j.hom.hom)).hom := by
        rw [hc]
        simp only [Category.assoc]
      _ = (b ≫ j) ≫ (G.innerIso (mS ≫ j.hom.hom)).hom := by rw [hb]
      _ = (b ≫ (M.innerIso mS).hom) ≫ j := by
        rw [Category.assoc, ← innerIso_hom_comp, ← Category.assoc]
  have hnorm : (CommGroupScheme.groupHom (f ≫ (normalizingAut i n).hom) ≫ iM) ≫ j =
      (b ≫ (M.innerIso mS).hom) ≫ j := by
    calc
      _ = CommGroupScheme.groupHom f ≫
          CommGroupScheme.groupHom (normalizingAut i n).hom ≫ i := by
        change ((CommGroupScheme.groupHom f ≫
          CommGroupScheme.groupHom (normalizingAut i n).hom) ≫ iM) ≫ j = _
        simp only [Category.assoc, hiM]
      _ = CommGroupScheme.groupHom f ≫ i ≫ (G.innerIso n.val).hom := by
        rw [← isNormalizingPoint_normalizingAut i n]
      _ = a ≫ j ≫ (G.innerIso n.val).hom := by
        have hfi : CommGroupScheme.groupHom f ≫ i = a ≫ j := by
          rw [← hiM, ← Category.assoc, hf]
        simpa only [Category.assoc] using
          congrArg (fun g => g ≫ (G.innerIso n.val).hom) hfi
      _ = _ := hconj
  let := hj.mono
  let : Mono j.hom.hom := Over.mono_of_mono_left _
  apply Grp.hom_ext
  apply (cancel_mono j.hom.hom).mp
  exact congrArg (fun g => g.hom.hom) hnorm.symm

/-- Characters of the Levi erase the inner conjugacy in the corrected map. -/
theorem character_comp_eq_of_normalizerCorrection
    (j : M ⟶ G) (hj : IsClosedSubgroup j)
    (i : T.toGrp ⟶ G) (iM : T.toGrp ⟶ M) (hiM : iM ≫ j = i)
    (a b : A.toGrp ⟶ M) (ha : IsCentral a)
    (f : A ⟶ T) (hf : CommGroupScheme.groupHom f ≫ iM = a)
    (z : rationalPoints G) (hb : b ≫ j = a ≫ j ≫ (G.innerIso z).hom)
    (mS mT : rationalPoints M) (n : normalizerPoints i)
    (hn : n.val = (mS ≫ j.hom.hom) * z * (mT ≫ j.hom.hom)⁻¹)
    (χ : rationalPoints M →* ℂˣ) :
    χ.comp (rationalPoints.map b) =
      χ.comp (rationalPoints.map
        (CommGroupScheme.groupHom (f ≫ (normalizingAut i n).hom) ≫ iM)) := by
  rw [← comp_innerIso_eq_normalizer_pullback j hj i iM hiM a b ha f hf z hb mS mT n hn]
  apply MonoidHom.ext
  intro x
  change χ (x ≫ b.hom.hom) =
    χ ((x ≫ b.hom.hom) ≫ (M.innerIso mS).hom.hom.hom)
  rw [comp_innerIso_hom, constantPoint_self, map_mul, map_mul, map_inv]
  exact (mul_inv_cancel_comm _ _).symm

namespace ParabolicRootPresentation

variable {P : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {p : P ⟶ G} {l : M ⟶ P} {a : A.toGrp ⟶ M}

/-- The original component map, acted on by an actual ambient normalizer
point and then mapped into the specified Levi through its torus factor. -/
def normalizerComponentPullback (pres : ParabolicRootPresentation p l a)
    (n : normalizerPoints pres.data.i) : A.toGrp ⟶ M :=
  CommGroupScheme.groupHom (pres.data.f ≫ (normalizingAut pres.data.i n).hom) ≫
    pres.leviTorusHom

end ParabolicRootPresentation

end Langlands.GroupScheme

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

namespace GeometricLemmaIntersectionDatum

variable {k : Type u} [Field k] [TopologicalSpace k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {P M N Q U : GroupScheme (Spec (CommRingCat.of k))}
  {p : P ⟶ G} {l : M ⟶ P} {r : N ⟶ P}
  {hp : IsParabolicSubgroup p} {hr : LeviSubgroup.IsGeometricUnipotentRadical r}
  {hl : IsRationalLeviSubgroup l} {hmul : IsIso (subgroupMultiplication l r)}
  {q : Q ⟶ G} {lQ : M ⟶ Q} {rQ : U ⟶ Q}
  {hq : IsParabolicSubgroup q} {hrQ : LeviSubgroup.IsGeometricUnipotentRadical rQ}
  {hlQ : IsRationalLeviSubgroup lQ} {hmulQ : IsIso (subgroupMultiplication lQ rQ)}
  {z : rationalPoints G}
  (D : GeometricLemmaIntersectionDatum p l r hp hr hl hmul
    q lQ rQ hq hrQ hlQ hmulQ z)
  {A : CommGroupScheme (Spec (CommRingCat.of k))} {a : A.toGrp ⟶ M}
  (pres : ParabolicRootPresentation p l a)

include D in
/-- An arbitrary supplied intersection datum for two parabolics with the
same Levi has a normalizer representative in its original double coset. -/
theorem exists_normalizerPoint_sameLevi (hLevi : lQ ≫ q = l ≫ p) :
    ∃ (mS mT : rationalPoints M) (n : normalizerPoints pres.data.i),
      n.val = (mS ≫ (l ≫ p).hom.hom) * z * (mT ≫ (l ≫ p).hom.hom)⁻¹ := by
  have htc : (D.targetCommonTorusHom ≫ D.lQ' ≫ D.q') ≫ (l ≫ p) =
      (D.t ≫ D.l' ≫ D.p' ≫ l ≫ p) ≫ (G.innerIso z).inv := by
    simpa only [Category.assoc, hLevi] using D.targetCommonTorusHom_comp
  have hst : (D.t ≫ D.l' ≫ D.p') ≫ (l ≫ p) =
      (D.targetCommonTorusHom ≫ D.lQ' ≫ D.q') ≫
        (l ≫ p) ≫ (G.innerIso z).hom := by
    have h := congrArg (fun g => g ≫ (G.innerIso z).hom) htc
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using h.symm
  apply exists_normalizerPoint_of_commonSplitTorus hl.isConnectedReductive
    (l ≫ p) (hl.isClosedSubgroup.comp hp.isClosedSubgroup)
    pres.data.i pres.isCompatible.maximalSplit pres.leviTorusHom
    pres.leviTorusHom_comp (D.t ≫ D.l' ≫ D.p')
    (D.targetCommonTorusHom ≫ D.lQ' ≫ D.q')
  · simpa only [Category.assoc] using D.isMaximalSplitTorus
  · simpa only [Category.assoc, hLevi] using
      D.targetCommonTorus_isMaximalSplitTorus_ambient
  · exact hst

/-- The original character pulled back by the actual piece maps equals its
normalizer pullback, for every character of the shared Levi. -/
theorem character_comp_piece_eq_normalizerPullback
    (hLevi : lQ ≫ q = l ≫ p)
    (b : A.toGrp ⟶ D.L') (hb : b ≫ D.lQ' ≫ D.q' = a)
    (mS mT : rationalPoints M) (n : normalizerPoints pres.data.i)
    (hn : n.val = (mS ≫ (l ≫ p).hom.hom) * z *
      (mT ≫ (l ≫ p).hom.hom)⁻¹)
    (χ : rationalPoints M →* ℂˣ) :
    χ.comp (rationalPoints.map (b ≫ D.φ.hom ≫ D.l' ≫ D.p')) =
      χ.comp (rationalPoints.map (pres.normalizerComponentPullback n)) := by
  apply character_comp_eq_of_normalizerCorrection (l ≫ p)
    (hl.isClosedSubgroup.comp hp.isClosedSubgroup)
    pres.data.i pres.leviTorusHom pres.leviTorusHom_comp
    a (b ≫ D.φ.hom ≫ D.l' ≫ D.p')
    pres.isCompatible.splitComponent.isCentralSplitTorus.isCentral
    pres.data.f pres.factor_comp_leviTorusHom z
  · calc
      _ = b ≫ (D.φ.hom ≫ D.l' ≫ D.p' ≫ l ≫ p) := by
        simp only [Category.assoc]
      _ = b ≫ D.lQ' ≫ D.q' ≫ (lQ ≫ q) ≫ (G.innerIso z).hom := by
        rw [D.φ_comp]
        simp only [Category.assoc]
      _ = a ≫ (l ≫ p) ≫ (G.innerIso z).hom := by
        simpa only [Category.assoc, hLevi] using
          congrArg (fun g => g ≫ (l ≫ p) ≫ (G.innerIso z).hom) hb
  · exact hn

section RealPart

variable [ValuativeRel k] [IsNonarchimedeanLocalField k]

open Langlands.AlgebraicGeometry.PointTopology

local instance : Mono pres.data.i.hom.hom.left :=
  pres.isCompatible.maximalSplit.isSplitSubtorus.mono

local instance : IsAffineHom pres.data.T.X.hom :=
  pres.isCompatible.maximalSplit.isSplitSubtorus.1.isAffineHom

local instance : IsAffine pres.data.T.X.left :=
  isAffine_of_isAffineHom pres.data.T.X.hom

local instance : TopologicalSpace (rationalPoints pres.data.T.toGrp) :=
  rationalPointTopology k pres.data.T.X

/-- The actual pulled-back unramified character has the inverse full Weyl
translate's restricted normalized real part. -/
theorem normalizedRealPart_piece_eq_of_normalizerCorrection
    (hLevi : lQ ≫ q = l ≫ p)
    (b : A.toGrp ⟶ D.L') (hb : b ≫ D.lQ' ≫ D.q' = a)
    (mS mT : rationalPoints M) (n : normalizerPoints pres.data.i)
    (hn : n.val = (mS ≫ (l ≫ p).hom.hom) * z *
      (mT ≫ (l ≫ p).hom.hom)⁻¹)
    (ψ : leviUnramifiedCharacters l hl) :
    letI := leviPointTopology l hl
    Plancherel.SplitTorus.normalizedRealPart
        pres.isCompatible.splitComponent.isCentralSplitTorus.1.1
        (ψ.val.toMonoidHom.comp
          (rationalPoints.map (b ≫ D.φ.hom ≫ D.l' ≫ D.p'))) =
      rationalCharacterRestrictReal (CommGroupScheme.groupHom pres.data.f)
        (relativeWeylFullRealAction pres.data.i
          ((QuotientGroup.mk n)⁻¹) (leviUnramifiedFullRealPart pres ψ)) := by
  let := leviPointTopology l hl
  let χT := ψ.val.toMonoidHom.comp (rationalPoints.map pres.leviTorusHom)
  let σ := normalizingAut pres.data.i n
  have hT := pres.isCompatible.maximalSplit.isSplitSubtorus.1
  have hχT : IsOpen (χT.ker : Set (rationalPoints pres.data.T.toGrp)) :=
    isOpen_ker_leviUnramifiedTorusCharacter pres ψ
  have hχσ := Plancherel.SplitTorus.isOpen_ker_comp_points σ.hom χT hχT
  have hσinv : normalizingAut pres.data.i n⁻¹ = σ.symm :=
    (isNormalizingPoint_normalizingAut pres.data.i n⁻¹).unique pres.data.i
      (isNormalizingPoint_normalizingAut pres.data.i n).inv
  have hreal : Plancherel.SplitTorus.normalizedRealPart hT
      (χT.comp (rationalPoints.map (CommGroupScheme.groupHom σ.hom))) =
      relativeWeylFullRealAction pres.data.i
        ((QuotientGroup.mk n)⁻¹) (leviUnramifiedFullRealPart pres ψ) := by
    change _ = relativeWeylFullRealAction pres.data.i
      (QuotientGroup.mk n⁻¹) (leviUnramifiedFullRealPart pres ψ)
    rw [relativeWeylFullRealAction_mk, hσinv]
    exact Plancherel.SplitTorus.normalizedRealPart_comp_points hT hT σ.hom χT hχT
  have hchar : ψ.val.toMonoidHom.comp
      (rationalPoints.map (b ≫ D.φ.hom ≫ D.l' ≫ D.p')) =
      (χT.comp (rationalPoints.map (CommGroupScheme.groupHom σ.hom))).comp
        (rationalPoints.map (CommGroupScheme.groupHom pres.data.f)) := by
    rw [D.character_comp_piece_eq_normalizerPullback pres hLevi b hb mS mT n hn]
    apply MonoidHom.ext
    intro x
    change ψ.val (x ≫ ((CommGroupScheme.groupHom pres.data.f ≫
      CommGroupScheme.groupHom σ.hom) ≫ pres.leviTorusHom).hom.hom) =
      ψ.val (((x ≫ (CommGroupScheme.groupHom pres.data.f).hom.hom) ≫
        (CommGroupScheme.groupHom σ.hom).hom.hom) ≫ pres.leviTorusHom.hom.hom)
    simp only [Grp.comp_hom_hom, Category.assoc]
  rw [hchar, Plancherel.SplitTorus.normalizedRealPart_comp_points
    pres.isCompatible.splitComponent.isCentralSplitTorus.1.1 hT pres.data.f _ hχσ, hreal]

end RealPart

end GeometricLemmaIntersectionDatum

end Langlands.Aubert.General.RepresentedParabolic
