import Langlands.Representation.Aubert.General.RationalSameLeviGenericIntertwinerStatement
import Langlands.Representation.Aubert.General.RepresentedSameLeviGenericIntertwinerStatement
import Langlands.Representation.Aubert.General.RepresentedStandardCuspidality
import Langlands.Representation.Exponents.ArbitraryParabolicLeviPoints
import Langlands.Representation.Exponents.ArbitraryParabolicLeviReparametrization
import Langlands.Representation.CompactCoefficient.GroupTransport
import Langlands.GroupScheme.Rational.ParabolicAmbientTransport
import Langlands.GroupScheme.Rational.PointContainmentFromDensity
import Langlands.GroupScheme.Rational.MinimalPseudoParabolicRangeReduction
import Langlands.GroupScheme.InnerAutomorphismHom

/-! # Reduction of the same-Levi intertwiner statement to represented parabolics -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General

open GroupScheme
open Langlands.AlgebraicGeometry.PointTopology

/-- A nonzero morphism, transported along isomorphisms of its source and target,
gives a nonzero morphism. -/
theorem exists_ne_zero_hom_of_isos {C : Type*} [Category C] [Limits.HasZeroMorphisms C]
    {A A' B B' : C} (α : A ≅ A') (β : B' ≅ B) (h : ∃ f : A' ⟶ B', f ≠ 0) :
    ∃ f : A ⟶ B, f ≠ 0 := by
  obtain ⟨f, hf⟩ := h
  refine ⟨α.hom ≫ f ≫ β.hom, fun h0 => hf ?_⟩
  calc f = α.inv ≫ (α.hom ≫ f ≫ β.hom) ≫ β.inv := by simp
    _ = 0 := by rw [h0]; simp

namespace RepresentedParabolic

variable {k : Type u} [Field k] [TopologicalSpace k]
  {G P M U : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance sameLeviReductionAmbientPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [T2Space k] [LocallyCompactSpace (rationalPoints G)]
  [NonarchimedeanGroup (rationalPoints G)]

/-- If the point images of a represented parabolic, its Levi and its radical are
three given subgroups, then the represented induction is the induction from
these subgroups, after pulling back along any point equivalence with the same
ambient values. -/
def leviInductionObjIsoOfPointImages (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
    (hp : IsParabolicSubgroup p) (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
    (hl : IsRationalLeviSubgroup l) (hmul : IsIso (subgroupMultiplication l r))
    {P' M' U' : Subgroup (rationalPoints G)}
    (h' : IsSemidirectDecomposition P' M' U') (hU' : IsClosed (U' : Set (rationalPoints G)))
    (hP : pointImage p = P') (hM : pointImage (l ≫ p) = M') (hN : pointImage (r ≫ p) = U')
    (e : letI := leviPointTopology l hl; rationalPoints M ≃ₜ* M')
    (he : ∀ x, (e x : rationalPoints G) = rationalPoints.map (l ≫ p) x)
    (X : letI := leviPointTopology l hl; SmoothRep.{0, u, v} ℂ (rationalPoints M)) :
    (leviInductionFunctor p l r hp hr hl hmul).obj X ≅
      (normalizedInductionFunctor h' hU').obj
        (letI := leviPointTopology l hl; SmoothRep.pullback e.symm X) := by
  letI := leviPointTopology l hl
  subst hP hM hN
  have hE : e = leviPointsEquiv p l hp hl := ContinuousMulEquiv.ext fun x => Subtype.ext (he x)
  subst hE
  exact Iso.refl _

/-- Transport of a nonzero morphism between two represented inductions sharing
the Levi `M` to the inductions from their point images. The twisted object is
`(σ ∘ e).twist ψ` on `M(F)`, where `e : M(F) ≃ M'` matches the point maps of
both parabolics and the unramified character `ψ` of `M(F)` is `χ ∘ e`. -/
theorem exists_ne_zero_normalizedInduction_of_leviInduction
    [ValuativeRel k] [IsNonarchimedeanLocalField k]
    {Q V : GroupScheme (Spec (CommRingCat.of k))} (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
    (hp : IsParabolicSubgroup p) (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
    (hl : IsRationalLeviSubgroup l) (hmul : IsIso (subgroupMultiplication l r))
    (q : Q ⟶ G) (lQ : M ⟶ Q) (rQ : V ⟶ Q)
    (hq : IsParabolicSubgroup q) (hrQ : LeviSubgroup.IsGeometricUnipotentRadical rQ)
    (hlQ : IsRationalLeviSubgroup lQ) (hmulQ : IsIso (subgroupMultiplication lQ rQ))
    {P' M' U' Q' V' : Subgroup (rationalPoints G)}
    (h' : IsSemidirectDecomposition P' M' U') (hU' : IsClosed (U' : Set (rationalPoints G)))
    (h'' : IsSemidirectDecomposition Q' M' V') (hV' : IsClosed (V' : Set (rationalPoints G)))
    (hP : pointImage p = P') (hM : pointImage (l ≫ p) = M') (hN : pointImage (r ≫ p) = U')
    (hQ : pointImage q = Q') (hMQ : pointImage (lQ ≫ q) = M')
    (hNQ : pointImage (rQ ≫ q) = V')
    (e : letI := leviPointTopology l hl; rationalPoints M ≃ₜ* M')
    (he : ∀ x, (e x : rationalPoints G) = rationalPoints.map (l ≫ p) x)
    (heQ : ∀ x, (e x : rationalPoints G) = rationalPoints.map (lQ ≫ q) x)
    (σ : SmoothRep.{0, u, v} ℂ M') (χ : M' →* ℂˣ) (hχ : IsOpen (χ.ker : Set M'))
    (ψ : letI : TopologicalSpace (rationalPoints M) :=
        (@rationalPointTopology k _ M.X
          (haveI := hl.isConnectedReductive.isAffineHom; isAffine_of_isAffineHom M.X.hom)
          _)
      Plancherel.unramifiedCharacters (fun chi => (Plancherel.rationalNormCharacters M chi).toMul))
    (hψ : letI := leviPointTopology l hl
      IsOpen (ψ.val.toMonoidHom.ker : Set (rationalPoints M)))
    (h : letI := leviPointTopology l hl
      ∃ f : (leviInductionFunctor p l r hp hr hl hmul).obj
          ((SmoothRep.pullback e σ).twist ψ.val.toMonoidHom hψ) ⟶
        (leviInductionFunctor q lQ rQ hq hrQ hlQ hmulQ).obj
          ((SmoothRep.pullback e σ).twist ψ.val.toMonoidHom hψ), f ≠ 0)
    (hψχ : letI := leviPointTopology l hl; ∀ m, ψ.val.toMonoidHom m = χ (e m)) :
    ∃ f : (normalizedInductionFunctor h' hU').obj (σ.twist χ hχ) ⟶
      (normalizedInductionFunctor h'' hV').obj (σ.twist χ hχ), f ≠ 0 := by
  let := leviPointTopology l hl
  let X := (SmoothRep.pullback e σ).twist ψ.val.toMonoidHom hψ
  let τ : σ.twist χ hχ ≅ SmoothRep.pullback e.symm X :=
    SmoothRep.mkIso (Representation.Equiv.mk (LinearEquiv.refl ℂ σ) fun m => by
      ext w
      change ((χ m : ℂˣ) : ℂ) • σ.representation m w =
        ((ψ.val.toMonoidHom (e.symm m) : ℂˣ) : ℂ) • σ.representation (e (e.symm m)) w
      rw [hψχ, e.apply_symm_apply])
  exact exists_ne_zero_hom_of_isos
    ((normalizedInductionFunctor h' hU').mapIso τ ≪≫
      (leviInductionObjIsoOfPointImages p l r hp hr hl hmul h' hU' hP hM hN e he X).symm)
    (leviInductionObjIsoOfPointImages q lQ rQ hq hrQ hlQ hmulQ h'' hV' hQ hMQ hNQ e heQ X ≪≫
      (normalizedInductionFunctor h'' hV').mapIso τ.symm) h

end RepresentedParabolic

namespace RationalPointFamily

open RepresentedParabolic

section SchemeIso

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of k))} (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

local instance sameLeviReductionAmbientAffine : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom

/-- The rational points of the represented standard Levi are the literal standard Levi. -/
theorem range_leviHom_carrier (K : Finset (SimpleRoot i ν)) :
    (SubgroupFunctor.range (Standard.leviHom i ν (rootSet i ν K))).carrier
      (Over.mk (𝟙 (Spec (CommRingCat.of k)))) = levi i ν K :=
  congrArg (fun S : SubgroupFunctor G => S.carrier (Over.mk (𝟙 _)))
    (Standard.isRepresentedBy_leviHom i ν (rootSet i ν K)).2

/-- The rational points of the represented standard parabolic are the literal
standard parabolic. -/
theorem pointImage_parabolicHom (K : Finset (SimpleRoot i ν)) :
    pointImage (Standard.parabolicHom i ν (rootSet i ν K)) = parabolic i ν K :=
  congrArg (fun S : SubgroupFunctor G => S.carrier (Over.mk (𝟙 _)))
    (Standard.isRepresentedBy_parabolicHom i ν (rootSet i ν K)).2

/-- The represented Levi of the standard parabolic has the literal standard Levi
as its rational points. -/
theorem pointImage_leviToParabolic_comp (K : Finset (SimpleRoot i ν)) :
    pointImage (Standard.leviToParabolic i ν (rootSet i ν K) ≫
      Standard.parabolicHom i ν (rootSet i ν K)) = levi i ν K := by
  rw [Standard.leviToParabolic_comp]
  exact range_leviHom_carrier i ν K

omit [IsAffineHom G.X.hom] in
/-- The inverse inner automorphism acts on rational points by `x ↦ g⁻¹ x g`. -/
theorem comp_innerIso_inv_rationalPoint (g x : rationalPoints G) :
    x ≫ (G.innerIso g).inv.hom.hom = g⁻¹ * x * g := by
  rw [← innerIso_inv_hom, comp_innerIso_hom, constantPoint_self, inv_inv]

omit [IsAffineHom G.X.hom] in
/-- The point image of a subgroup conjugated by `g` is the conjugate subgroup. -/
theorem pointImage_comp_innerIso {H : GroupScheme (Spec (CommRingCat.of k))}
    (j : H ⟶ G) (g : rationalPoints G) :
    pointImage (j ≫ (G.innerIso g).hom) = conjugateSubgroup g (pointImage j) := by
  ext x
  rw [mem_pointImage_comp_innerIso, mem_conjugateSubgroup]

/-- Under the Levi conjugacy hypothesis, conjugating `L_J` by `g⁻¹` gives the
points of `L_I`. -/
theorem pointImage_leviHom_comp_innerIso_inv (I J : Finset (SimpleRoot i ν))
    (g : rationalPoints G)
    (hIJ : ∀ x : rationalPoints G, x ∈ levi i ν J ↔ g⁻¹ * x * g ∈ levi i ν I) :
    pointImage (Standard.leviHom i ν (rootSet i ν J) ≫ (G.innerIso g⁻¹).hom) =
      levi i ν I := by
  ext x
  rw [mem_pointImage_comp_innerIso, inv_inv, pointImage_eq_range_carrier,
    range_leviHom_carrier, hIJ]
  simp [mul_assoc]

section LocalField

variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/-- The conjugate of the represented Levi `L_J` by `g⁻¹` and the represented
Levi `L_I` have the same image on every test scheme. -/
theorem range_leviHom_comp_innerIso_inv (I J : Finset (SimpleRoot i ν))
    (g : rationalPoints G)
    (hIJ : ∀ x : rationalPoints G, x ∈ levi i ν J ↔ g⁻¹ * x * g ∈ levi i ν I)
    (hLI : IsConnectedReductive (Standard.leviScheme i ν (rootSet i ν I)))
    (hLJ : IsConnectedReductive (Standard.leviScheme i ν (rootSet i ν J))) :
    SubgroupFunctor.range (Standard.leviHom i ν (rootSet i ν J) ≫ (G.innerIso g⁻¹).hom) =
      SubgroupFunctor.range (Standard.leviHom i ν (rootSet i ν I)) := by
  have hpts := pointImage_leviHom_comp_innerIso_inv i ν I J g hIJ
  apply le_antisymm
  · have := hLJ.smooth
    have := hLJ.isAffineHom
    have := hLJ.connectedSpace
    refine SubgroupFunctor.range_le_of_localField_points
      (Standard.isClosedSubgroup_leviHom i ν _) ?_
    intro x hx
    have hx' : x ∈ pointImage
        (Standard.leviHom i ν (rootSet i ν J) ≫ (G.innerIso g⁻¹).hom) := hx
    rw [hpts] at hx'
    rw [range_leviHom_carrier]
    exact hx'
  · have := hLI.smooth
    have := hLI.isAffineHom
    have := hLI.connectedSpace
    refine SubgroupFunctor.range_le_of_localField_points
      ((Standard.isClosedSubgroup_leviHom i ν _).comp_iso (G.innerIso g⁻¹)) ?_
    intro x hx
    rw [range_leviHom_carrier] at hx
    change x ∈ pointImage
      (Standard.leviHom i ν (rootSet i ν J) ≫ (G.innerIso g⁻¹).hom)
    rw [hpts]
    exact hx

/-- The scheme isomorphism `L_J ≅ L_I` induced by inverse conjugation by `g`. -/
def leviSchemeIsoOfConj (I J : Finset (SimpleRoot i ν)) (g : rationalPoints G)
    (hIJ : ∀ x : rationalPoints G, x ∈ levi i ν J ↔ g⁻¹ * x * g ∈ levi i ν I)
    (hLI : IsConnectedReductive (Standard.leviScheme i ν (rootSet i ν I)))
    (hLJ : IsConnectedReductive (Standard.leviScheme i ν (rootSet i ν J))) :
    Standard.leviScheme i ν (rootSet i ν J) ≅ Standard.leviScheme i ν (rootSet i ν I) :=
  IsClosedSubgroup.sourceIsoOfRangeEq
    ((Standard.isClosedSubgroup_leviHom i ν _).comp_iso (G.innerIso g⁻¹))
    (Standard.isClosedSubgroup_leviHom i ν _)
    (range_leviHom_comp_innerIso_inv i ν I J g hIJ hLI hLJ)

/-- The isomorphism `L_J ≅ L_I` intertwines the two Levi inclusions with
inverse conjugation by `g`. -/
theorem leviSchemeIsoOfConj_hom_comp (I J : Finset (SimpleRoot i ν)) (g : rationalPoints G)
    (hIJ : ∀ x : rationalPoints G, x ∈ levi i ν J ↔ g⁻¹ * x * g ∈ levi i ν I)
    (hLI : IsConnectedReductive (Standard.leviScheme i ν (rootSet i ν I)))
    (hLJ : IsConnectedReductive (Standard.leviScheme i ν (rootSet i ν J))) :
    (leviSchemeIsoOfConj i ν I J g hIJ hLI hLJ).hom ≫ Standard.leviHom i ν (rootSet i ν I) =
      Standard.leviHom i ν (rootSet i ν J) ≫ (G.innerIso g).inv := by
  rw [← innerIso_inv_hom]
  exact IsClosedSubgroup.sourceIsoOfRangeEq_hom_comp _ _ _

end LocalField

end SchemeIso

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency.types false in
/-- The same-Levi nonzero-intertwiner statement for the literal standard Levi
subgroups follows from its version for represented parabolics sharing one Levi
scheme. The second represented parabolic is the conjugate of `P_I` by `g`, with
Levi scheme `L_J` embedded through inverse conjugation by `g`. -/
theorem rationalSameLeviGenericNonzeroIntertwiner_of_represented
    (h : RepresentedSameLeviGenericNonzeroIntertwinerStatement.{u, v}) :
    RationalSameLeviGenericNonzeroIntertwinerStatement.{u, v} := by
  intro k _ _ _ _ G hG T i hi _ _ _ ν hν hStandard hU I J g hIJ hLJ σ hσ hσa
  have := hG.isAffineHom
  have : T2Space k := BruhatTits.localField_t2Space k
  let : TopologicalSpace (rationalPoints G) := pointTopology
  obtain ⟨hpJ, hlJ, hrJ, hmulJ⟩ :=
    standard_representatives_geometric_of_standardCocharacter i ν hStandard hG hi hν J
  let : TopologicalSpace (rationalPoints (Standard.leviScheme i ν (rootSet i ν J))) :=
    leviPointTopology (Standard.leviToParabolic i ν (rootSet i ν J)) hlJ
  have := leviPoints_nonarchimedeanGroup (Standard.parabolicHom i ν (rootSet i ν J))
    (Standard.leviToParabolic i ν (rootSet i ν J)) hpJ hlJ
  obtain ⟨hpI, hlI, hrI, hmulI⟩ :=
    standard_representatives_geometric_of_standardCocharacter i ν hStandard hG hi hν I
  let eL := leviSchemeIsoOfConj i ν I J g hIJ hlI.isConnectedReductive hLJ
  have hq := hpI.comp_iso (G.innerIso g)
  have hlQ := hlI.iso_comp eL
  have hmulQ := isIso_subgroupMultiplication_iso_comp eL hmulI
  have hcomm : Standard.leviToParabolic i ν (rootSet i ν J) ≫
      Standard.parabolicHom i ν (rootSet i ν J) =
      (eL.hom ≫ Standard.leviToParabolic i ν (rootSet i ν I)) ≫
        (Standard.parabolicHom i ν (rootSet i ν I) ≫ (G.innerIso g).hom) := by
    rw [Standard.leviToParabolic_comp, Category.assoc,
      ← Category.assoc (Standard.leviToParabolic i ν (rootSet i ν I)),
      Standard.leviToParabolic_comp, ← Category.assoc, leviSchemeIsoOfConj_hom_comp,
      Category.assoc, Iso.inv_hom_id, Category.comp_id]
  let e : rationalPoints (Standard.leviScheme i ν (rootSet i ν J)) ≃ₜ* levi i ν J :=
    leviRationalPointHomeomorph i ν J
  have he : ∀ x, (e x : rationalPoints G) = rationalPoints.map
      (Standard.leviToParabolic i ν (rootSet i ν J) ≫
        Standard.parabolicHom i ν (rootSet i ν J)) x := by
    intro x
    rw [Standard.leviToParabolic_comp]
    rfl
  have heQ : ∀ x, (e x : rationalPoints G) = rationalPoints.map
      ((eL.hom ≫ Standard.leviToParabolic i ν (rootSet i ν I)) ≫
        (Standard.parabolicHom i ν (rootSet i ν I) ≫ (G.innerIso g).hom)) x := by
    intro x
    rw [← hcomm]
    exact he x
  have hPQ : pointImage (Standard.parabolicHom i ν (rootSet i ν I) ≫ (G.innerIso g).hom) =
      conjugateSubgroup g (parabolic i ν I) := by
    rw [pointImage_comp_innerIso, pointImage_parabolicHom]
  have hMQ : pointImage ((eL.hom ≫ Standard.leviToParabolic i ν (rootSet i ν I)) ≫
      (Standard.parabolicHom i ν (rootSet i ν I) ≫ (G.innerIso g).hom)) = levi i ν J := by
    rw [← hcomm]
    exact pointImage_leviToParabolic_comp i ν J
  have hNQ : pointImage (Standard.unipotentToParabolic i ν (rootSet i ν I) ≫
      (Standard.parabolicHom i ν (rootSet i ν I) ≫ (G.innerIso g).hom)) =
      conjugateSubgroup g (unipotent i ν I) := by
    rw [← Category.assoc, pointImage_comp_innerIso, standard_unipotent_pointImage]
  have hσ' : (SmoothRep.pullback e σ).IsIrreducible :=
    (isIrreducible_comp_continuousMulEquiv_iff σ.representation e).mpr hσ
  have hσa' : (SmoothRep.pullback e σ).IsAdmissible :=
    isAdmissible_comp_continuousMulEquiv σ.representation e hσa
  obtain ⟨poly, hpoly, hgen⟩ := h k G hG _ _ _ _ _ _ _ _ hpJ hlJ hrJ hmulJ _ _ _ hq hlQ hrI
    hmulQ hcomm (SmoothRep.pullback e σ) hσ' hσa'
  refine ⟨poly, hpoly, fun χ hχ => ?_⟩
  refine exists_ne_zero_normalizedInduction_of_leviInduction
    (Standard.parabolicHom i ν (rootSet i ν J)) (Standard.leviToParabolic i ν (rootSet i ν J))
    (Standard.unipotentToParabolic i ν (rootSet i ν J)) hpJ hrJ hlJ hmulJ
    (Standard.parabolicHom i ν (rootSet i ν I) ≫ (G.innerIso g).hom)
    (eL.hom ≫ Standard.leviToParabolic i ν (rootSet i ν I))
    (Standard.unipotentToParabolic i ν (rootSet i ν I)) hq hrI hlQ hmulQ
    (isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν J) (hU J)
    ((isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν
      I).conjugateWithLevi g hIJ) (isClosed_conjugateSubgroup g (hU I))
    (pointImage_parabolicHom i ν J) (pointImage_leviToParabolic_comp i ν J)
    (standard_unipotent_pointImage i ν J) hPQ hMQ hNQ e he heQ σ χ.val.toMonoidHom _
    ((leviRationalUnramifiedCharacterHomeomorph i ν J).symm χ) ?c2 ?c3 ?c4
  case c3 =>
    obtain ⟨f', hf'⟩ := hgen ((leviRationalUnramifiedCharacterHomeomorph i ν J).symm χ) hχ
    exact ⟨f', hf'⟩
  case c4 => exact fun m => rfl
  case c2 => exact Plancherel.unramifiedCharacter_isOpen_ker _ _

end RationalPointFamily

end Langlands.Aubert.General
