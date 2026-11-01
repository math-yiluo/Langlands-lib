import Langlands.Representation.Derivative.MirabolicPhiMinusMackey
import Langlands.Representation.Derivative.MirabolicProductMinusCompatibilityStatement
import Langlands.Representation.Derivative.MirabolicProductMinusRightBoundary
import Langlands.Representation.Derivative.MirabolicProductRestrictionTransport
import Langlands.Group.GL.MirabolicMixedOrbitData

/-!
# Assembly of the positive-rank right `Φ⁻` sequence from its two orbit pieces

The right mixed product `τ × ρ` on `P_(k+r+3)`, after the rank cast, is compact
induction from the transported right mixed subgroup `H = rightInducing k r`.
Given an ordered enumeration of the two `(H, Q)` orbits with the published
representatives, the localized Mackey sequence of
`Derivative/MirabolicPhiMinusMackey` gives a natural short exact sequence for
`Φ⁻(τ × ρ)`. This file shows that natural identifications of the two
normalized localized orbit pieces with `(Φ⁻τ) × ρ` and `(Ψ⁻τ) × ρ|P` yield the
sequence of `RightPhiShortExact` at the given ranks.
-/

noncomputable section

open CategoryTheory

namespace Langlands.Derivative.MirabolicProductMinus

open GeneralLinear HarmonicAnalysis GeneralLinear.Mirabolic
open GeneralLinear.Mirabolic.MixedProduct GeneralLinear.Mirabolic.MixedOrbit

universe uF uV uR uG uC vC

/-! ## Generic category helpers -/

section Generic

variable {R : Type uR} [CommRing R] {G : Type uG} [Group G]

/-- Twisting by a character, as an endofunctor of `Rep R G`. -/
def repTwistFunctor (χ : G →* Rˣ) : Rep.{uV} R G ⥤ Rep.{uV} R G where
  obj A := Rep.of (twist χ A.ρ)
  map f := Rep.ofHom (twistIntertwining χ f.hom)
  map_id _ := rfl
  map_comp _ _ := rfl

variable {C : Type uC} [Category.{vC} C]

/-- Pointwise short exactness survives whiskering by the twist functor, which keeps
the underlying linear maps. -/
theorem exact_whiskerRight_repTwist {A B D : C ⥤ Rep.{uV} R G} (χ : G →* Rˣ)
    (i : A ⟶ B) (q : B ⟶ D)
    (h : ∀ X, Function.Injective (i.app X).hom ∧
      LinearMap.range (i.app X).hom.toLinearMap = LinearMap.ker (q.app X).hom.toLinearMap ∧
      Function.Surjective (q.app X).hom) :
    ∀ X, Function.Injective ((Functor.whiskerRight i (repTwistFunctor χ)).app X).hom ∧
      LinearMap.range ((Functor.whiskerRight i (repTwistFunctor χ)).app X).hom.toLinearMap =
        LinearMap.ker ((Functor.whiskerRight q (repTwistFunctor χ)).app X).hom.toLinearMap ∧
      Function.Surjective ((Functor.whiskerRight q (repTwistFunctor χ)).app X).hom :=
  h

variable [TopologicalSpace G]

/-- A natural transformation between the underlying algebraic functors of two
functors into smooth representations is a natural transformation between them. -/
def liftNatTrans {F₁ F₂ : C ⥤ SmoothRep.{0, uG, uV} ℂ G}
    (η : F₁ ⋙ SmoothRep.toRep ⟶ F₂ ⋙ SmoothRep.toRep) : F₁ ⟶ F₂ where
  app X := ObjectProperty.homMk (η.app X)
  naturality _ _ f := SmoothRep.toRep.map_injective (η.naturality f)

/-- Pointwise short exactness of the underlying algebraic transformations is pointwise
short exactness of the lifted ones. -/
theorem exact_liftNatTrans {F₁ F₂ F₃ : C ⥤ SmoothRep.{0, uG, uV} ℂ G}
    (η₁ : F₁ ⋙ SmoothRep.toRep ⟶ F₂ ⋙ SmoothRep.toRep)
    (η₂ : F₂ ⋙ SmoothRep.toRep ⟶ F₃ ⋙ SmoothRep.toRep)
    (h : ∀ X, Function.Injective (η₁.app X).hom ∧
      LinearMap.range (η₁.app X).hom.toLinearMap = LinearMap.ker (η₂.app X).hom.toLinearMap ∧
      Function.Surjective (η₂.app X).hom) :
    ∀ X, Function.Injective (SmoothRep.hom ((liftNatTrans η₁).app X)) ∧
      LinearMap.range (SmoothRep.hom ((liftNatTrans η₁).app X)).toLinearMap =
        LinearMap.ker (SmoothRep.hom ((liftNatTrans η₂).app X)).toLinearMap ∧
      Function.Surjective (SmoothRep.hom ((liftNatTrans η₂).app X)) :=
  h

/-- A pointwise short exact pair of algebraic transformations, identified at the three
positions with the underlying algebraic functors of functors into smooth
representations, gives a pointwise short exact pair of transformations between those. -/
theorem exists_exact_lift {A B D : C ⥤ Rep.{uV} ℂ G} {F₁ F₂ F₃ : C ⥤ SmoothRep.{0, uG, uV} ℂ G}
    (i : A ⟶ B) (q : B ⟶ D) (eA : A ≅ F₁ ⋙ SmoothRep.toRep) (eB : B ≅ F₂ ⋙ SmoothRep.toRep)
    (eD : D ≅ F₃ ⋙ SmoothRep.toRep)
    (h : ∀ X, Function.Injective (i.app X).hom ∧
      LinearMap.range (i.app X).hom.toLinearMap = LinearMap.ker (q.app X).hom.toLinearMap ∧
      Function.Surjective (q.app X).hom) :
    ∃ (i' : F₁ ⟶ F₂) (q' : F₂ ⟶ F₃), ∀ X,
      Function.Injective (SmoothRep.hom (i'.app X)) ∧
      LinearMap.range (SmoothRep.hom (i'.app X)).toLinearMap =
        LinearMap.ker (SmoothRep.hom (q'.app X)).toLinearMap ∧
      Function.Surjective (SmoothRep.hom (q'.app X)) :=
  ⟨liftNatTrans (eA.symm.hom ≫ i ≫ eB.hom), liftNatTrans (eB.inv ≫ q ≫ eD.hom),
    exact_liftNatTrans _ _ (Mirabolic.exact_comp_isos i q eA.symm eB eD h)⟩

@[simp] theorem hom_liftNatTrans_app {F₁ F₂ : C ⥤ SmoothRep.{0, uG, uV} ℂ G}
    (η : F₁ ⋙ SmoothRep.toRep ⟶ F₂ ⋙ SmoothRep.toRep) (X : C) :
    SmoothRep.hom ((liftNatTrans η).app X) = (η.app X).hom := rfl

end Generic

/-! ## The transported right mixed product -/

section Transport

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

/-- The rank cast `P_(k+r+3) ≅ P_((k+1)+(r+1)+1)` as an isomorphism of topological
groups. -/
def rightPhiCast (T : F.TopologicalData) (k r : ℕ) :
    letI := T.topology
    mirabolic (k + r + 2) F.Carrier ≃ₜ* mirabolic (k + 1 + (r + 1)) F.Carrier :=
  letI := T.topology
  { toMulEquiv := (rankCast (R := F.Carrier) (totalRank_eq k r)).symm
    continuous_toFun := continuous_rankCast_symm _
    continuous_invFun := continuous_rankCast _ }

/-- The published rank-cast pullback is pullback along the same entrywise cast. -/
theorem mirabolicCastHom_eq_rightPhiCast (T : F.TopologicalData) (k r : ℕ) :
    letI := T.topology
    mirabolicCastHom (R := F.Carrier) (Nat.succ_add k (r + 1)) =
      (rightPhiCast T k r).toMonoidHom := by
  let := T.topology
  apply MonoidHom.ext
  intro x
  apply Subtype.ext
  apply Units.ext
  ext i j
  rw [mirabolicCastHom_apply]
  rfl

/-- The coefficient of the right mixed product pulled back to `H = rightInducing k r`:
`h ↦ χ_R(h) (τ(p) ⊗ ρ(a))`, with `(p, a)` the blocks of the transported `h`. -/
def rightOrbitInput (T : F.TopologicalData) (k r : ℕ) :
    letI := T.topology
    (SmoothRep.{0, uF, uV} ℂ (mirabolic (r + 1) F.Carrier) ×
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear (k + 1) F.Carrier)) ⥤
      SmoothRep.{0, uF, uV} ℂ (rightInducing k r F.Carrier) :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup (k + 1 + (r + 1) + 1)
  MixedProductTensor.externalFunctor ⋙
    MixedProductTensor.pullbackFunctor rightProjection continuous_rightProjection ⋙
      SmoothRep.twistFunctor (T.rightCharacter (k + 1) (r + 1)).toMonoidHom
        (T.rightCharacter (k + 1) (r + 1)).isOpen_ker ⋙
        Mirabolic.continuousPullbackFunctor (rightInducingHom k r F.Carrier)
          (continuous_rightInducingHom k r F.Carrier)

/-- Compact induction from `rightSubgroup (k+1) (r+1)` pulled back along the cast is
compact induction from `rightInducing k r` of the pulled-back coefficient. -/
def rightPhiTransportEquiv (T : F.TopologicalData) (k r : ℕ)
    (X : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (mirabolic (r + 1) F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear (k + 1) F.Carrier)) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup (k + r + 1 + 1 + 1)
    letI := T.generalLinearTopologicalGroup (k + 1 + (r + 1) + 1)
    Representation.Equiv
      ((Mirabolic.continuousPullbackFunctor (mirabolicCastHom (Nat.succ_add k (r + 1)))
        (continuous_mirabolicCastHom _)).obj
          ((T.rightMixedProductFunctor (k + 1) (r + 1)).obj X)).representation
      (Induction.compactInduced (G := mirabolic (k + r + 1 + 1) F.Carrier)
        (rightInducing k r F.Carrier)
        ((rightOrbitInput T k r).obj X).representation) :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup (k + r + 1 + 1 + 1)
  letI := T.generalLinearTopologicalGroup (k + 1 + (r + 1) + 1)
  (equivOfRepresentationEq (congrArg _ (mirabolicCastHom_eq_rightPhiCast T k r))).trans
    (Induction.compactInducedTransport (rightPhiCast T k r) (rightInducing k r F.Carrier)
      (rightSubgroup (k + 1) (r + 1) F.Carrier) (fun _ => Iff.rfl)
      ((rightOrbitInput T k r).obj X).representation
      (twist (T.rightCharacter (k + 1) (r + 1)).toMonoidHom
        (rightInducingRepresentation X.1.representation X.2.representation))
      (LinearEquiv.refl ℂ _) (fun _ _ => rfl))

/-- The cast right mixed product is compact induction from `rightInducing k r`. -/
def rightPhiTransportIso (T : F.TopologicalData) (k r : ℕ) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup (k + r + 1 + 1 + 1)
    T.rightMixedProductFunctor.{uF, uV} (k + 1) (r + 1) ⋙
        mirabolicRankCast T (Nat.succ_add k (r + 1)) ≅
      rightOrbitInput T k r ⋙ SmoothRep.toRep ⋙
        Induction.compactInductionFunctor (G := mirabolic (k + r + 1 + 1) F.Carrier)
          (rightInducing k r F.Carrier) :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup (k + r + 1 + 1 + 1)
  letI := T.generalLinearTopologicalGroup (k + 1 + (r + 1) + 1)
  Functor.isoWhiskerLeft (T.rightMixedProductFunctor (k + 1) (r + 1))
      (mirabolicRankCastIso T (Nat.succ_add k (r + 1))) ≪≫
    NatIso.ofComponents (fun X => SmoothRep.mkIso (rightPhiTransportEquiv T k r X)) (by
      intro X Y f
      apply SmoothRep.toRep.map_injective
      apply Rep.hom_ext
      apply Representation.IntertwiningMap.ext
      apply LinearMap.ext
      intro u
      exact (Induction.compactInducedTransport_natural (rightPhiCast T k r)
        (rightInducing k r F.Carrier) (rightSubgroup (k + 1) (r + 1) F.Carrier)
        (fun _ => Iff.rfl) ((rightOrbitInput T k r).obj X).representation
        (twist (T.rightCharacter (k + 1) (r + 1)).toMonoidHom
          (rightInducingRepresentation X.1.representation X.2.representation))
        (LinearEquiv.refl ℂ _) (fun _ _ => rfl)
        ((rightOrbitInput T k r).obj Y).representation
        (twist (T.rightCharacter (k + 1) (r + 1)).toMonoidHom
          (rightInducingRepresentation Y.1.representation Y.2.representation))
        (LinearEquiv.refl ℂ _) (fun _ _ => rfl)
        (SmoothRep.hom ((rightOrbitInput T k r).map f))
        (twistIntertwining (T.rightCharacter (k + 1) (r + 1)).toMonoidHom
          (MixedProductTensor.pullbackMap rightProjection
            (MixedProductTensor.externalMap (SmoothRep.hom f.1) (SmoothRep.hom f.2))))
        (fun _ => rfl) u))

end Transport

/-! ## Assembly -/

section Assembly

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

/-- Twisting commutes with forgetting smoothness, on the nose. -/
def twistToRepIso {G : Type uG} [Group G] [TopologicalSpace G] (χ : G →* ℂˣ)
    (hχ : IsOpen (χ.ker : Set G)) :
    SmoothRep.twistFunctor.{0, uG, uV} χ hχ ⋙ SmoothRep.toRep ≅
      SmoothRep.toRep ⋙ repTwistFunctor χ :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)

/-- The localized orbit piece at `w`, normalized like `Φ⁻`: the coefficient of the right
mixed product on `H`, the published orbit piece at `w`, the localization on `Q`, and the
twist by `|det|^(-1/2)`. -/
abbrev rightPhiPiece (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (k r : ℕ)
    (w : mirabolic (k + r + 1 + 1) F.Carrier) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup (k + r + 1 + 1 + 1)
    (SmoothRep.{0, uF, uV} ℂ (mirabolic (r + 1) F.Carrier) ×
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear (k + 1) F.Carrier)) ⥤
      Rep.{max uF uV} ℂ (mirabolic (k + r + 1) F.Carrier) :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup (k + r + 1 + 1 + 1)
  (rightOrbitInput T k r ⋙
    (Geometric.orbitPiece (R := ℂ) (G := mirabolic (k + r + 1 + 1) F.Carrier)
      (rightInducing k r F.Carrier) (plusSubgroup (k + r + 1) F.Carrier) w ⋙
    Mirabolic.plusPhiLocalization ψ (k + r + 1))) ⋙
    repTwistFunctor (Mirabolic.phiMinusCharacter T (k + r + 1))

/-- The middle term: the twisted localization of the compact induction from `H` is the
algebraic functor underlying `Φ⁻(τ × ρ)`, through associators, the transport and the
twist identification. -/
def rightPhiMiddleIso (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (k r : ℕ) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup (k + r + 1 + 1 + 1)
    (rightOrbitInput.{uF, uV} T k r ⋙
        ((SmoothRep.toRep ⋙ Induction.compactInductionFunctor
          (G := mirabolic (k + r + 1 + 1) F.Carrier) (rightInducing k r F.Carrier)) ⋙
          Mirabolic.phiMinusUnnormalized T ψ (k + r + 1) ⋙ SmoothRep.toRep)) ⋙
        repTwistFunctor (Mirabolic.phiMinusCharacter T (k + r + 1)) ≅
      rightPhiProduct.{uF, uV} T ψ k (r + 1) ⋙
        SmoothRep.toRep (G := mirabolic (k + r + 1) F.Carrier) :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup (k + r + 1 + 1 + 1)
  let In := rightOrbitInput.{uF, uV} T k r
  let C := SmoothRep.toRep ⋙ Induction.compactInductionFunctor.{0, uF, uV} (R := ℂ)
    (G := mirabolic (k + r + 1 + 1) F.Carrier)
    (rightInducing k r F.Carrier)
  let U := Mirabolic.phiMinusUnnormalized.{max uF uV} T ψ (k + r + 1)
  let χ := Mirabolic.phiMinusCharacter T (k + r + 1)
  let hχ := Mirabolic.isOpen_ker_phiMinusCharacter T (k + r + 1)
  let eT : (U ⋙ SmoothRep.toRep) ⋙ repTwistFunctor χ ≅
      Mirabolic.phiMinus T ψ (k + r + 1) ⋙ SmoothRep.toRep :=
    Functor.associator U SmoothRep.toRep (repTwistFunctor χ) ≪≫
      Functor.isoWhiskerLeft U (twistToRepIso χ hχ).symm ≪≫
      (Functor.associator U (SmoothRep.twistFunctor χ hχ) SmoothRep.toRep).symm
  Functor.associator In (C ⋙ U ⋙ SmoothRep.toRep) (repTwistFunctor χ) ≪≫
    Functor.isoWhiskerLeft In
      (Functor.associator C (U ⋙ SmoothRep.toRep) (repTwistFunctor χ) ≪≫
        Functor.isoWhiskerLeft C eT) ≪≫
    (Functor.associator In C (Mirabolic.phiMinus T ψ (k + r + 1) ⋙ SmoothRep.toRep)).symm ≪≫
    Functor.isoWhiskerRight (rightPhiTransportIso.{uF, uV} T k r).symm
      (Mirabolic.phiMinus T ψ (k + r + 1) ⋙ SmoothRep.toRep) ≪≫
    Functor.associator (T.rightMixedProductFunctor (k + 1) (r + 1))
      (mirabolicRankCast T (Nat.succ_add k (r + 1)))
      (Mirabolic.phiMinus T ψ (k + r + 1) ⋙ SmoothRep.toRep) ≪≫
    Functor.isoWhiskerLeft (T.rightMixedProductFunctor (k + 1) (r + 1))
      (Functor.associator (mirabolicRankCast T (Nat.succ_add k (r + 1)))
        (Mirabolic.phiMinus T ψ (k + r + 1)) SmoothRep.toRep).symm ≪≫
    (Functor.associator (T.rightMixedProductFunctor (k + 1) (r + 1))
      (mirabolicRankCast T (Nat.succ_add k (r + 1)) ⋙ Mirabolic.phiMinus T ψ (k + r + 1))
      SmoothRep.toRep).symm

set_option maxHeartbeats 800000 in
/-- Natural identifications of the two normalized localized orbit pieces with
`(Φ⁻τ) × ρ` and `(Ψ⁻τ) × ρ|P`, for an ordered enumeration of the two orbits with the
published representatives, give the positive-rank right `Φ⁻` sequence. -/
theorem rightPhiShortExact_of_pieces (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (k r : ℕ)
    (s : letI := T.topology; letI := T.generalLinearTopologicalGroup (k + r + 1 + 1 + 1)
      Geometric.OrderedDoubleCosets (rightInducing k r F.Carrier)
        (plusSubgroup (k + r + 1) F.Carrier) 2)
    (hs : letI := T.topology; letI := T.generalLinearTopologicalGroup (k + r + 1 + 1 + 1)
      s.representative = rightRepresentative k r F.Carrier)
    (E₀ : letI := T.topology; letI := T.generalLinearTopologicalGroup (k + r + 1 + 1 + 1)
      rightPhiPiece.{uF, uV} T ψ k r (rightRepresentative k r F.Carrier 0) ≅
        rightPhiSubobject.{uF, uV} T ψ k r ⋙ SmoothRep.toRep)
    (E₁ : letI := T.topology; letI := T.generalLinearTopologicalGroup (k + r + 1 + 1 + 1)
      rightPhiPiece.{uF, uV} T ψ k r (rightRepresentative k r F.Carrier 1) ≅
        rightPhiQuotient.{uF, uV} T k (r + 1) ⋙
          SmoothRep.toRep (G := mirabolic (k + r + 1) F.Carrier)) :
    letI := T.topology
    ∃ (i : rightPhiSubobject.{uF, uV} T ψ k r ⟶ rightPhiProduct T ψ k (r + 1))
      (q : rightPhiProduct.{uF, uV} T ψ k (r + 1) ⟶ rightPhiQuotient T k (r + 1)),
      ∀ X,
        Function.Injective (SmoothRep.hom (i.app X)) ∧
        LinearMap.range (SmoothRep.hom (i.app X)).toLinearMap =
          LinearMap.ker (SmoothRep.hom (q.app X)).toLinearMap ∧
        Function.Surjective (SmoothRep.hom (q.app X)) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup (k + r + 1 + 1 + 1)
  let := T.fieldT2
  have key := Mirabolic.exists_exact_phiMinusUnnormalized_compactInduction.{uF, uV} T ψ
    (k + r + 1) (rightInducing k r F.Carrier) (rightInducing_isClosed k r F.Carrier) s
  rw [hs] at key
  obtain ⟨i, q, h⟩ := key
  let χ := Mirabolic.phiMinusCharacter T (k + r + 1)
  let i₁ := Functor.whiskerRight (Functor.whiskerLeft (rightOrbitInput T k r) i)
    (repTwistFunctor χ)
  let q₁ := Functor.whiskerRight (Functor.whiskerLeft (rightOrbitInput T k r) q)
    (repTwistFunctor χ)
  have h₁ := exact_whiskerRight_repTwist χ (Functor.whiskerLeft (rightOrbitInput T k r) i)
    (Functor.whiskerLeft (rightOrbitInput T k r) q) (fun X => h ((rightOrbitInput T k r).obj X))
  exact exists_exact_lift i₁ q₁ E₀ (rightPhiMiddleIso T ψ k r) E₁ h₁

end Assembly

end Langlands.Derivative.MirabolicProductMinus
