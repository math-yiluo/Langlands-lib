import Langlands.Representation.Plancherel.UnramifiedRationalJacquetGeometryFiniteness
import Langlands.Representation.Geometric.RepresentedGeometricLemmaKnownCocharacters
import Langlands.Representation.Geometric.ClosedSubgroupOrbitOrdering
import Langlands.Representation.Exponents.ArbitraryParabolicQuotientCompactStatement

/-! Native Jacquet finiteness from the remaining finite-geometry and compactness targets. -/

noncomputable section
set_option maxHeartbeats 20000

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct NNReal

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

universe u

variable {k : Type u} [Field k] [TopologicalSpace k] [T2Space k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {P M N Q L U : GroupScheme (Spec (CommRingCat.of k))}
  {p : P ⟶ G} {l : M ⟶ P} {n : N ⟶ P}
  {hp : IsParabolicSubgroup p} {hn : LeviSubgroup.IsGeometricUnipotentRadical n}
  {hl : IsRationalLeviSubgroup l} {hmul : IsIso (subgroupMultiplication l n)}
  {q : Q ⟶ G} {lQ : L ⟶ Q} {nQ : U ⟶ Q}
  {hq : IsParabolicSubgroup q} {hnQ : LeviSubgroup.IsGeometricUnipotentRadical nQ}
  {hlQ : IsRationalLeviSubgroup lQ} {hmulQ : IsIso (subgroupMultiplication lQ nQ)}

local instance orderedGeometryPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  [T2Space (rationalPoints G)] [SigmaCompactSpace (rationalPoints G)]

/-- Finite torus-adapted representatives and known original cocharacters give
an actual open-prefix orbit ordering together with all intersection data and
simultaneous realizations at its inverse representatives. -/
theorem exists_orderedIntersectionDataOfKnownCocharacters
    (hD : RepresentedParabolicDoubleCosetStatement.{u}) (hG : IsConnectedReductive G)
    (χP χQ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    (hP : SubgroupFunctor.range p = Dynamic.parabolic χP)
    (hM : SubgroupFunctor.range (l ≫ p) = Dynamic.centralizer χP)
    (hN : SubgroupFunctor.range (n ≫ p) = Dynamic.unipotent χP)
    (hQ : SubgroupFunctor.range q = Dynamic.parabolic χQ)
    (hL : SubgroupFunctor.range (lQ ≫ q) = Dynamic.centralizer χQ)
    (hU : SubgroupFunctor.range (nQ ≫ q) = Dynamic.unipotent χQ) :
    ∃ (m : ℕ) (t : Geometric.OrderedDoubleCosets (pointImage p) (pointImage q) m)
      (D : ∀ j : Fin m, GeometricLemmaIntersectionDatum p l n hp hn hl hmul
        q lQ nQ hq hnQ hlQ hmulQ (t.representative j)⁻¹),
      Nonempty (∀ j : Fin m, (D j).DynamicRealization) := by
  obtain ⟨hfinite, hrepresentative⟩ := hD k G hG P M Q L p l hp hl q lQ hq hlQ
  obtain ⟨m, ⟨t⟩⟩ := Geometric.closedSubgroupOrbitOrdering (rationalPoints G)
    (pointImage p) (pointImage q)
    (isClosed_pointImage p hp.isClosedSubgroup)
    (isClosed_pointImage q hq.isClosedSubgroup) hfinite
  have hgood (g : rationalPoints G) :
      ∃ z : rationalPoints G, DoubleCoset.mk (pointImage p) (pointImage q) z =
        DoubleCoset.mk (pointImage p) (pointImage q) g ∧
        Nonempty (GeometricLemmaIntersectionDatum p l n hp hn hl hmul
          q lQ nQ hq hnQ hlQ hmulQ z) := by
    obtain ⟨z, hz, T, i, hi, ⟨ta, hta⟩, ⟨tb, htb⟩⟩ := hrepresentative g
    exact ⟨z, hz, ⟨geometricLemmaIntersectionDatumOfKnownCocharacters
      χP χQ hP hM hN hQ hL hU z i hi ta hta tb htb⟩⟩
  choose z hz hdatum using fun j : Fin m => hgood (t.representative j)⁻¹
  let t' := t.replaceRepresentatives (fun j => (z j)⁻¹)
    (fun j => by simpa only [inv_inv] using hz j)
  let D : ∀ j : Fin m, GeometricLemmaIntersectionDatum p l n hp hn hl hmul
      q lQ nQ hq hnQ hlQ hmulQ (t'.representative j)⁻¹ := fun j => by
    have he : (t'.representative j)⁻¹ = z j := inv_inv _
    rw [he]
    exact Classical.choice (hdatum j)
  exact ⟨m, t', D, ⟨fun j => GeometricLemmaIntersectionDatum.dynamicRealizationOfKnownCocharacters
    χP χQ hP hM hN hQ hL hU (D j)⟩⟩

end Langlands.Aubert.General.RepresentedParabolic

namespace Langlands.Plancherel.RationalNormalized

open GroupScheme Aubert.General.RepresentedParabolic Induction
open Langlands.AlgebraicGeometry.PointTopology

universe u

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {A : CommGroupScheme (Spec (CommRingCat.of F))}
  {G M P N : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [Smooth G.X.hom]
  {p : P ⟶ G} {l : M ⟶ P} {a : A.toGrp ⟶ M}
  (r : ParabolicRootPresentation p l a)
  {n : N ⟶ P} (hn : LeviSubgroup.IsGeometricUnipotentRadical n)
  {Q L U : GroupScheme (Spec (CommRingCat.of F))}
  {q : Q ⟶ G} {lQ : L ⟶ Q} {nQ : U ⟶ Q}
  {hq : IsParabolicSubgroup q} {hnQ : LeviSubgroup.IsGeometricUnipotentRadical nQ}
  {hlQ : IsRationalLeviSubgroup lQ} {hmulQ : IsIso (subgroupMultiplication lQ nQ)}

local instance structuralAmbientAffine : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom
local instance structuralPointTopology : TopologicalSpace (rationalPoints G) :=
  rationalPointTopology F G.X
local instance structuralFieldT2 : T2Space F := BruhatTits.localField_t2Space F

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]

/-- The two remaining global structural assertions construct the actual finite
ordered intersection geometry. The known source and output cocharacters remove
any need for a universal parabolic-dynamic premise. -/
def nativeJacquetFiniteOrbitGeometryOfStructural
    (hD : RepresentedParabolicDoubleCosetStatement.{u})
    (hC : ArbitraryParabolicQuotientCompactStatement.{u})
    (hG : IsConnectedReductive G)
    (χQ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
    (hQ : SubgroupFunctor.range q = Dynamic.parabolic χQ)
    (hL : SubgroupFunctor.range (lQ ≫ q) = Dynamic.centralizer χQ)
    (hU : SubgroupFunctor.range (nQ ≫ q) = Dynamic.unipotent χQ) :
    NativeJacquetFiniteOrbitGeometry (r := r) (hn := hn)
      (q := q) (lQ := lQ) (nQ := nQ) (hq := hq) (hnQ := hnQ)
      (hlQ := hlQ) (hmulQ := hmulQ) := by
  apply Classical.choice
  let : T2Space (rationalPoints G) := rationalPoint_t2Space F G
  let : SecondCountableTopology (rationalPoints G) :=
    Aubert.General.RationalPointFamily.reductiveRationalPoint_secondCountable F G hG
  let : SigmaCompactSpace (rationalPoints G) :=
    sigmaCompactSpace_of_locallyCompact_secondCountable
  let χP := CommGroupScheme.groupHom r.splitComponentCocharacter ≫ a ≫ l ≫ p
  have hP : SubgroupFunctor.range p = Dynamic.parabolic χP :=
    r.parabolic_eq_splitComponentCocharacter
  have hM : SubgroupFunctor.range (l ≫ p) = Dynamic.centralizer χP :=
    r.levi_eq_splitComponentCocharacter
  have hN : SubgroupFunctor.range (n ≫ p) = Dynamic.unipotent χP :=
    r.range_comp_radical_eq hn
  obtain ⟨m, t, D, ⟨R⟩⟩ := exists_orderedIntersectionDataOfKnownCocharacters
    (hp := r.isCompatible.parabolic) (hn := hn) (hl := r.isCompatible.levi)
    (hmul := r.isIso_subgroupMultiplication_of_radical hn)
    (hnQ := hnQ) (hmulQ := hmulQ) hD hG χP χQ hP hM hN hQ hL hU
  refine ⟨{ length := m, ordering := t, intersection := D
            realization := R, quotient_compact := ?_ }⟩
  intro j
  let := hlQ.isConnectedReductive.isAffineHom
  let := leviPointTopology lQ hlQ
  let := leviPoints_locallyCompactSpace q lQ hq hlQ
  let := leviPoints_nonarchimedeanGroup q lQ hq hlQ
  exact hC F L hlQ.isConnectedReductive (D j).Q' (D j).q' (D j).hq'

end Langlands.Plancherel.RationalNormalized

namespace Langlands.Plancherel

open GroupScheme Aubert.General.RepresentedParabolic Induction
open Langlands.AlgebraicGeometry.PointTopology

universe u uV

/-- Conditional assembly of the unchanged global target. Only finite
parabolic double cosets with adapted tori and original parabolic quotient
compactness remain as global structural premises. -/
theorem rationalSupercuspidalJacquetFamilyFinite_of_structural
    (hD : RepresentedParabolicDoubleCosetStatement.{u})
    (hC : ArbitraryParabolicQuotientCompactStatement.{u}) :
    RationalSupercuspidalJacquetFamilyFiniteStatement.{u, uV} := by
  intro F _ _ _ _ G hG
  have := hG.isAffineHom
  have := hG.smooth
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  let : T2Space F := BruhatTits.localField_t2Space F
  let : T2Space (rationalPoints G) := rationalPoint_t2Space F G
  let : LocallyCompactSpace (rationalPoints G) := rationalPoint_locallyCompactSpace F G
  let : NonarchimedeanGroup (rationalPoints G) :=
    Aubert.General.RationalPointFamily.affineRationalPoint_nonarchimedeanGroup G
  intro A M P U p l a r
  have := r.isCompatible.levi.isConnectedReductive.isAffineHom
  have : IsAffine M.X.left := isAffine_of_isAffineHom M.X.hom
  intro n hn h hU hproj hcompact E _ _ σ _hSmooth hσ _hIrreducible hcusp χ J _hJ
  let : CompactSpace (LeftQuotient (pointImage p)) := hcompact
  let d := Dynamic.affineDecompositionModel χ
  have hq : IsParabolicSubgroup d.parabolicHom :=
    isParabolicSubgroup_of_range_eq_dynamicParabolic hG d.parabolicHom
      d.parabolic_closed χ d.parabolic_rep.2
  let : IsAffineHom d.parabolic.X.hom := d.parabolic_closed.isAffineHom
  have hnQ : LeviSubgroup.IsGeometricUnipotentRadical d.unipotentHom :=
    (dynamicGeometricUnipotentRadical F G hG χ d.parabolic d.unipotent
      d.parabolicHom d.unipotentHom d.parabolic_rep d.unipotent_rep).leviSubgroup_of_unipotentFieldExtension
        unipotentFieldExtensionStatement
  have hlQ : IsRationalLeviSubgroup d.leviHom :=
    ⟨inferInstance, d.levi_closed,
      dynamicCentralizerReductive F G hG χ d.levi (d.leviHom ≫ d.parabolicHom)
        (d.levi_closed.comp d.parabolic_closed) d.levi_rep,
      ⟨d.unipotent, d.unipotentHom, hnQ, d.multiplication_isIso⟩⟩
  let S := RationalNormalized.nativeJacquetFiniteOrbitGeometryOfStructural r hn
    (hq := hq) (hnQ := hnQ) (hlQ := hlQ) (hmulQ := d.multiplication_isIso)
    hD hC hG χ d.parabolic_rep.2 d.levi_rep.2 d.unipotent_rep.2
  exact RationalNormalized.outputJacquet_fixedModule_finite_of_geometry r hn h hU
    hG hproj σ hσ hcusp χ d.levi_rep.2 d.unipotent_rep.2
    S.ordering S.intersection S.realization S.quotient_compact J

end Langlands.Plancherel
