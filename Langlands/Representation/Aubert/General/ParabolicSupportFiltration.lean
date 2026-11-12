import Langlands.Representation.Aubert.General.CorrectedFiltration
import Langlands.Representation.Geometric.SmoothSupportFiltration
import Langlands.Representation.Geometric.CompactSmoothComparison
import Langlands.Representation.Geometric.ClosedSubgroupMackeyProof
import Langlands.Representation.Filtration.Transport
import Langlands.Representation.Filtration.IsoTransport
import Langlands.Representation.Filtration.ExactSmoothTransport
import Langlands.Representation.Jacquet.LocalizationTransport
import Langlands.Representation.Jacquet.LocalizationExactnessProof
import Langlands.Representation.Twist.SmoothProof
import Langlands.Representation.Category.RestrictionSubquotients

/-!
# Support filtration of Jacquet restriction after parabolic induction

For two actual semidirect decompositions `P = M ⋉ U` and `Q = L ⋉ V` of
subgroups of a nonarchimedean locally compact group, this module filters the
composite of normalized induction from `M` and normalized Jacquet restriction
to `L` by the images of the functions supported on the initial unions of a
specified ordered `Q`-orbit cover of `P \ G`.  Its successive quotients are
naturally the normalized `V`-coinvariants of the compact Mackey orbit pieces.
-/

noncomputable section

universe uG uV uC vC

open CategoryTheory

namespace Langlands.Aubert.General

section Generic

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G]
  {P M U Q L V : Subgroup G}

section Inducing

variable (dP : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))

/-- The inducing covariance of normalized induction: inflation along the actual
Levi projection followed by the positive half Haar character of `U` on `P`. -/
def parabolicInducingFunctor : SmoothRep.{0, uG, uV} ℂ M ⥤ Rep.{uV} ℂ P :=
  inflationFunctor dP ⋙ (inductionCharacter U P hU dP.le_normalizer).twistFunctor

/-- Normalized induction restricted to `Q` is the raw restricted smooth induction
of the inducing covariance. -/
theorem normalizedInduction_restrict_eq (Q : Subgroup G) :
    normalizedInductionFunctor.{uG, uV} dP hU ⋙ SmoothRep.toRep ⋙ Rep.resFunctor Q.subtype =
      parabolicInducingFunctor dP hU ⋙ Geometric.rawRestrictedSmoothInduction P Q :=
  rfl

/-- The support filtration of normalized induction restricted to `Q`. -/
def inductionSupportFiltration {m : ℕ} (s : Geometric.OrderedDoubleCosets P Q m) :
    RepFunctorFiltration
      (normalizedInductionFunctor.{uG, uV} dP hU ⋙ SmoothRep.toRep ⋙
        Rep.resFunctor Q.subtype) m :=
  s.rawSmoothSupportFiltration.precomp (parabolicInducingFunctor dP hU)

/-- The inducing covariance is smooth when the Levi projection is continuous. -/
theorem isSmooth_parabolicInducingFunctor_obj (hp : Continuous dP.projection)
    (A : SmoothRep.{0, uG, uV} ℂ M) :
    IsSmooth ((parabolicInducingFunctor dP hU).obj A).ρ :=
  (isSmooth_twist_iff (inductionCharacter U P hU dP.le_normalizer).toMonoidHom
    (A.representation.comp dP.projection)
    (inductionCharacter U P hU dP.le_normalizer).isOpen_ker).mpr
      (isSmooth_comp dP.projection hp A.isSmooth)

/-- The inducing covariance in the full smooth category of `P`. -/
def smoothParabolicInducingFunctor (hp : Continuous dP.projection) :
    SmoothRep.{0, uG, uV} ℂ M ⥤ SmoothRep.{0, uG, uV} ℂ P where
  obj A := SmoothRep.of ((parabolicInducingFunctor dP hU).obj A).ρ
    (isSmooth_parabolicInducingFunctor_obj dP hU hp A)
  map f := ObjectProperty.homMk ((parabolicInducingFunctor dP hU).map f)
  map_id A := by
    apply ObjectProperty.hom_ext
    exact (parabolicInducingFunctor dP hU).map_id A
  map_comp f g := by
    apply ObjectProperty.hom_ext
    exact (parabolicInducingFunctor dP hU).map_comp f g

@[simp]
theorem smoothParabolicInducingFunctor_toRep (hp : Continuous dP.projection) :
    smoothParabolicInducingFunctor.{uG, uV} dP hU hp ⋙ SmoothRep.toRep =
      parabolicInducingFunctor dP hU :=
  rfl

end Inducing

section Coinvariants

variable (dQ : IsSemidirectDecomposition Q L V) (hV : IsClosed (V : Set G))

/-- The inverse half Haar character of `V` on `L`, as a smooth character. -/
def parabolicInverseHalfCharacter : Induction.SmoothCharacter ℂ L where
  toMonoidHom := HaarModulus.closedInverseHalfCharacter V hV L dQ.levi_le_normalizer
  isOpen_ker := HaarModulus.isOpen_ker_closedInverseHalfCharacter V hV L dQ.levi_le_normalizer

/-- The inclusion of the Levi into the top subgroup of the parabolic. -/
def leviToTopParabolic : L →* (⊤ : Subgroup Q) :=
  (Subgroup.topEquiv).symm.toMonoidHom.comp (Subgroup.inclusion dQ.levi_le)

omit [LocallyCompactSpace G] [NonarchimedeanGroup G] in
theorem continuous_leviToTopParabolic : Continuous (leviToTopParabolic dQ) :=
  ((continuous_subtype_val.subtype_mk _).subtype_mk _)

/-- Normalized `V`-coinvariants on all representations of the parabolic `Q`,
with output on `L`. -/
def parabolicCoinvariantsFunctor : Rep.{uV} ℂ Q ⥤ Rep.{uV} ℂ L :=
  letI : (V.subgroupOf Q).Normal := dQ.normal
  Jacquet.Localization.functor (V.subgroupOf Q) 1 ⊤
      (by simp only [Subgroup.normalizer_eq_top, le_refl])
      (Jacquet.Localization.isInvariant_one _ _ _) ⋙
    Rep.resFunctor (leviToTopParabolic dQ) ⋙
      (parabolicInverseHalfCharacter dQ hV).twistFunctor

@[simp]
theorem parabolicCoinvariantsFunctor_map_mk {A B : Rep.{uV} ℂ Q} (f : A ⟶ B) (x : A) :
    ((parabolicCoinvariantsFunctor dQ hV).map f).hom
      (Jacquet.Localization.mk A.ρ (V.subgroupOf Q) 1 x) =
        Jacquet.Localization.mk B.ρ (V.subgroupOf Q) 1 (f.hom x) :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 800000 in
/-- Restricting an ambient representation to `Q` leaves its `V`-coinvariants
and their normalized `L`-action unchanged. -/
def parabolicCoinvariantsRestrictionIso :
    SmoothRep.toRep ⋙ Rep.resFunctor Q.subtype ⋙ parabolicCoinvariantsFunctor.{uG, uV} dQ hV ≅
      jacquetFunctor dQ hV ⋙ SmoothRep.toRep := by
  let eN := Subgroup.subgroupOfEquivOfLe dQ.unipotent_le
  let e := fun A : SmoothRep.{0, uG, uV} ℂ G =>
    Jacquet.Localization.transportEquiv
      (A.representation.comp Q.subtype) A.representation
      (V.subgroupOf Q) V 1 1 eN
      (LinearEquiv.refl ℂ A) (fun _ _ => rfl) (fun _ => rfl)
  refine NatIso.ofComponents (fun A => Rep.mkIso {
    toLinearEquiv := e A
    isIntertwining' := ?_ }) ?_
  · intro m
    apply LinearMap.ext
    intro x
    obtain ⟨y, rfl⟩ := Jacquet.Localization.mk_surjective
      (A.representation.comp Q.subtype) (V.subgroupOf Q) 1 x
    change e A ((((parabolicInverseHalfCharacter dQ hV).toMonoidHom m : ℂˣ) : ℂ) •
        Jacquet.Localization.mk _ _ 1 (A.representation (m : G) y)) =
      (((parabolicInverseHalfCharacter dQ hV).toMonoidHom m : ℂˣ) : ℂ) •
        Jacquet.Localization.mk _ _ 1 (A.representation (m : G) y)
    rw [map_smul]
    rfl
  · intro A B f
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    obtain ⟨y, rfl⟩ := Jacquet.Localization.mk_surjective
      (A.representation.comp Q.subtype) (V.subgroupOf Q) 1 x
    change e B (Jacquet.Localization.mk
      (B.representation.comp Q.subtype) (V.subgroupOf Q) 1 (SmoothRep.hom f y)) =
      Jacquet.Localization.mk B.representation V 1 (SmoothRep.hom f y)
    rfl

/-- Smooth input representations of `Q` have smooth normalized coinvariants. -/
theorem isSmooth_parabolicCoinvariantsFunctor_obj (A : SmoothRep.{0, uG, uV} ℂ Q) :
    IsSmooth ((parabolicCoinvariantsFunctor dQ hV).obj A.obj).ρ := by
  let : (V.subgroupOf Q).Normal := dQ.normal
  let hn : (⊤ : Subgroup Q) ≤ Subgroup.normalizer (V.subgroupOf Q) := by
    simp only [Subgroup.normalizer_eq_top, le_refl]
  exact (isSmooth_twist_iff (parabolicInverseHalfCharacter dQ hV).toMonoidHom _
    (parabolicInverseHalfCharacter dQ hV).isOpen_ker).mpr
      (isSmooth_comp (leviToTopParabolic dQ) (continuous_leviToTopParabolic dQ)
        (Jacquet.Localization.isSmooth_action A.representation
          (V.subgroupOf Q) 1 ⊤ hn (Jacquet.Localization.isInvariant_one _ _ hn) A.isSmooth))

/-- The same normalized coinvariants with their smoothness bundled. -/
def smoothParabolicCoinvariantsFunctor :
    SmoothRep.{0, uG, uV} ℂ Q ⥤ SmoothRep.{0, uG, uV} ℂ L where
  obj A := SmoothRep.of ((parabolicCoinvariantsFunctor dQ hV).obj A.obj).ρ
    (isSmooth_parabolicCoinvariantsFunctor_obj dQ hV A)
  map f := ObjectProperty.homMk ((parabolicCoinvariantsFunctor dQ hV).map f.hom)
  map_id A := by
    apply ObjectProperty.hom_ext
    exact (parabolicCoinvariantsFunctor dQ hV).map_id A.obj
  map_comp f g := by
    apply ObjectProperty.hom_ext
    exact (parabolicCoinvariantsFunctor dQ hV).map_comp f.hom g.hom

@[simp]
theorem smoothParabolicCoinvariantsFunctor_toRep :
    smoothParabolicCoinvariantsFunctor.{uG, uV} dQ hV ⋙ SmoothRep.toRep =
      SmoothRep.toRep ⋙ parabolicCoinvariantsFunctor dQ hV :=
  rfl

/-- If `V` is a limit of compact subgroups inside `Q`, the smooth normalized
coinvariant functor is exact on the full smooth category of `Q`. -/
theorem smoothParabolicCoinvariantsFunctor_exact
    (hVc : Jacquet.Localization.IsLimitOfCompactSubgroups (V.subgroupOf Q)) :
    Derivative.Mirabolic.MapsShortExactIntertwiners
      (smoothParabolicCoinvariantsFunctor.{uG, uV} dQ hV) := by
  let : (V.subgroupOf Q).Normal := dQ.normal
  let hn : (⊤ : Subgroup Q) ≤ Subgroup.normalizer (V.subgroupOf Q) := by
    simp only [Subgroup.normalizer_eq_top, le_refl]
  intro A B C f g hf hg hex
  exact ⟨Jacquet.Localization.map_injective_of_smooth
    (V.subgroupOf Q) hVc 1 (IsLocallyConstant.const 1) ⊤ hn
    (Jacquet.Localization.isInvariant_one _ _ hn) (SmoothRep.hom f) hf B.isSmooth,
    Jacquet.Localization.map_range_eq_ker (V.subgroupOf Q) 1 ⊤ hn
      (Jacquet.Localization.isInvariant_one _ _ hn) (SmoothRep.hom f) (SmoothRep.hom g) hg hex,
    Jacquet.Localization.map_surjective (V.subgroupOf Q) 1 ⊤ hn
      (Jacquet.Localization.isInvariant_one _ _ hn) (SmoothRep.hom g) hg⟩

variable {C : Type uC} [Category.{vC} C] {F : C ⥤ SmoothRep.{0, uG, uV} ℂ Q}

/-- The quotient of two nested coinvariant images is naturally the normalized
coinvariants of the corresponding quotient. -/
def parabolicCoinvariantsImageQuotientIso
    (hVc : Jacquet.Localization.IsLimitOfCompactSubgroups (V.subgroupOf Q))
    (S T : RepSubfunctor (F ⋙ SmoothRep.toRep)) (hST : ∀ X, S.obj X ≤ T.obj X) :
    (S.exactImage (smoothParabolicCoinvariantsFunctor dQ hV)).quotientFunctor
        (T.exactImage (smoothParabolicCoinvariantsFunctor dQ hV)) ≅
      S.quotientFunctor T ⋙ parabolicCoinvariantsFunctor dQ hV :=
  S.exactImageQuotientIso T (smoothParabolicCoinvariantsFunctor dQ hV)
    (smoothParabolicCoinvariantsFunctor_exact dQ hV hVc) hST

end Coinvariants

section JacquetImage

variable (dP : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
  (dQ : IsSemidirectDecomposition Q L V) (hV : IsClosed (V : Set G))

/-- The image of a natural `Q`-stable subspace of normalized induction in the
normalized `V`-coinvariants, as a subfunctor of the induction–Jacquet composite. -/
def jacquetImageSubfunctor
    (S : RepSubfunctor
      (normalizedInductionFunctor.{uG, uV} dP hU ⋙ SmoothRep.toRep ⋙
        Rep.resFunctor Q.subtype)) :
    RepSubfunctor
      (normalizedInductionFunctor.{uG, uV} dP hU ⋙
        jacquetFunctor.{uG, max uG uV} dQ hV ⋙ SmoothRep.toRep) where
  obj A := CorrectedFiltration.jacquetImage dQ hV
    ((normalizedInductionFunctor dP hU).obj A) (S.obj A).toSubmodule
    (fun x hx _ hv => (S.obj A).apply_mem_toSubmodule ⟨x, hx⟩ hv)
  map_mem := by
    intro A B f x hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨SmoothRep.hom ((normalizedInductionFunctor dP hU).map f) y, S.map_mem f hy, rfl⟩

set_option maxHeartbeats 800000 in
/-- The support-image filtration of the induction–Jacquet composite. -/
def jacquetSupportFiltration {m : ℕ} (s : Geometric.OrderedDoubleCosets P Q m) :
    RepFunctorFiltration
      (normalizedInductionFunctor.{uG, uV} dP hU ⋙
        jacquetFunctor.{uG, max uG uV} dQ hV ⋙ SmoothRep.toRep) m := by
  let t := inductionSupportFiltration.{uG, uV} dP hU s
  refine {
    step j := jacquetImageSubfunctor dP hU dQ hV (t.step j)
    monotone A := ?_
    zero A := ?_
    top A := ?_ }
  · intro i j hij x hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨y, t.monotone A hij hy, rfl⟩
  · apply Subrepresentation.toSubmodule_injective
    change Submodule.map _ ((t.step 0).obj A).toSubmodule = ⊥
    rw [t.zero A]
    exact Submodule.map_bot _
  · apply le_antisymm le_top
    intro x _
    obtain ⟨y, rfl⟩ := Jacquet.Localization.mk_surjective
      ((normalizedInductionFunctor dP hU).obj A).representation V 1 x
    exact ⟨y, t.top A ▸ Submodule.mem_top, rfl⟩

/-- Parabolic coinvariants of restricted induction are the induction–Jacquet
composite, with the same vector classes. -/
def inductionCoinvariantsRestrictionIso :
    (normalizedInductionFunctor.{uG, uV} dP hU ⋙
      SmoothRep.restrictSubgroupFunctor Q) ⋙
        smoothParabolicCoinvariantsFunctor.{uG, max uG uV} dQ hV ⋙ SmoothRep.toRep ≅
      normalizedInductionFunctor dP hU ⋙ jacquetFunctor dQ hV ⋙ SmoothRep.toRep :=
  Functor.isoWhiskerLeft (normalizedInductionFunctor dP hU)
    (parabolicCoinvariantsRestrictionIso dQ hV)

private theorem repSubfunctor_eq_of_obj_eq
    {R : Type*} [CommRing R] {H : Type*} [Monoid H]
    {C : Type*} [Category C] {F : C ⥤ Rep R H} {S T : RepSubfunctor F}
    (h : ∀ X, S.obj X = T.obj X) : S = T := by
  cases S with
  | mk Sobj Smap =>
    cases T with
    | mk Tobj Tmap =>
      have heq : Sobj = Tobj := funext h
      cases heq
      rfl

variable
  (S T : RepSubfunctor
    (normalizedInductionFunctor.{uG, uV} dP hU ⋙ SmoothRep.toRep ⋙ Rep.resFunctor Q.subtype))

set_option maxHeartbeats 800000 in
/-- Transporting the mapped-inclusion image along the same-vector-class
comparison gives exactly the ambient support-image subfunctor. -/
theorem jacquetImage_eq_isoTransport_exactImage :
    (S.exactImage
        (smoothParabolicCoinvariantsFunctor.{uG, max uG uV} dQ hV)).isoTransport
        (inductionCoinvariantsRestrictionIso dP hU dQ hV) =
      jacquetImageSubfunctor dP hU dQ hV S := by
  let I := normalizedInductionFunctor.{uG, uV} dP hU
  let e := inductionCoinvariantsRestrictionIso dP hU dQ hV
  apply repSubfunctor_eq_of_obj_eq
  intro A
  apply SetLike.ext
  intro x
  change (∃ y, SmoothRep.hom
      ((smoothParabolicCoinvariantsFunctor dQ hV).map
        ((S.smoothInclusion (F := I ⋙ SmoothRep.restrictSubgroupFunctor Q)).app A))
        y = (e.inv.app A).hom x) ↔
    ∃ y ∈ (S.obj A), Jacquet.Localization.mk (I.obj A).representation V 1 y = x
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨z, rfl⟩ := Jacquet.Localization.mk_surjective
      (S.obj A).toRepresentation (V.subgroupOf Q) 1 y
    refine ⟨z.val, z.property, ?_⟩
    have he := congrArg (e.hom.app A).hom hy
    exact he.trans (Rep.hom_inv_apply _ _ (e.app A) x)
  · rintro ⟨y, hy, rfl⟩
    refine ⟨Jacquet.Localization.mk (S.obj A).toRepresentation
      (V.subgroupOf Q) 1 ⟨y, hy⟩, ?_⟩
    apply (Representation.equivOfIso (e.app A)).injective
    exact (Rep.hom_inv_apply _ _ (e.app A) _).symm

set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 800000 in
/-- Exactness on `Q` identifies the quotient of two nested ambient images with
the normalized coinvariants of the corresponding induction quotient. -/
def jacquetImageQuotientIso
    (hVc : Jacquet.Localization.IsLimitOfCompactSubgroups (V.subgroupOf Q))
    (hST : ∀ A, S.obj A ≤ T.obj A) :
    (jacquetImageSubfunctor dP hU dQ hV S).quotientFunctor
        (jacquetImageSubfunctor dP hU dQ hV T) ≅
      S.quotientFunctor T ⋙ parabolicCoinvariantsFunctor dQ hV := by
  let J := smoothParabolicCoinvariantsFunctor.{uG, max uG uV} dQ hV
  let e := inductionCoinvariantsRestrictionIso dP hU dQ hV
  let SI := S.exactImage
    (F := normalizedInductionFunctor dP hU ⋙ SmoothRep.restrictSubgroupFunctor Q) J
  let TI := T.exactImage
    (F := normalizedInductionFunctor dP hU ⋙ SmoothRep.restrictSubgroupFunctor Q) J
  let A := jacquetImageSubfunctor dP hU dQ hV S
  let B := jacquetImageSubfunctor dP hU dQ hV T
  have hS : SI.isoTransport e = A :=
    jacquetImage_eq_isoTransport_exactImage dP hU dQ hV S
  have hT : TI.isoTransport e = B :=
    jacquetImage_eq_isoTransport_exactImage dP hU dQ hV T
  have hExact : SI.quotientFunctor TI ≅ S.quotientFunctor T ⋙
      parabolicCoinvariantsFunctor dQ hV :=
    parabolicCoinvariantsImageQuotientIso
      (F := normalizedInductionFunctor dP hU ⋙ SmoothRep.restrictSubgroupFunctor Q)
      dQ hV hVc S T hST
  have hTransport : (SI.isoTransport e).quotientFunctor (TI.isoTransport e) ≅
      SI.quotientFunctor TI := (SI.isoTransportQuotientIso TI e).symm
  change A.quotientFunctor B ≅ _
  clear_value SI TI A B e
  exact eqToIso (congrArg₂ (fun X Y => X.quotientFunctor Y) hS.symm hT.symm) ≪≫
    hTransport ≪≫ hExact

set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 800000 in
/-- At each support index, the Jacquet support grade is the normalized
coinvariants of the induction support grade. -/
def jacquetSupportGradedIso
    (hVc : Jacquet.Localization.IsLimitOfCompactSubgroups (V.subgroupOf Q))
    {m : ℕ} (s : Geometric.OrderedDoubleCosets P Q m) (i : Fin m) :
    (jacquetSupportFiltration.{uG, uV} dP hU dQ hV s).graded i ≅
      (inductionSupportFiltration dP hU s).graded i ⋙
        parabolicCoinvariantsFunctor dQ hV := by
  let t := inductionSupportFiltration.{uG, uV} dP hU s
  exact jacquetImageQuotientIso dP hU dQ hV
    (t.step i.castSucc) (t.step i.succ) hVc (fun A => t.step_le_next A i)

end JacquetImage

section Orbit

variable (dP : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
  (hp : Continuous dP.projection)
  [CompactSpace (Induction.LeftQuotient P)]

/-- Compactness of `P \ G` identifies the compact and smooth support quotients,
with the same functions and indices. -/
def inductionSupportCompactIso {m : ℕ} (s : Geometric.OrderedDoubleCosets P Q m)
    (i : Fin m) :
    smoothParabolicInducingFunctor.{uG, uV} dP hU hp ⋙
        (s.supportFiltration (R := ℂ)).graded i ≅
      (inductionSupportFiltration dP hU s).graded i :=
  Functor.isoWhiskerLeft (parabolicInducingFunctor dP hU)
    (s.rawSupportGradedCompactSmoothIso (R := ℂ) i)

variable [T2Space G] [SigmaCompactSpace G]

/-- Each induction support quotient is naturally the compactly induced
stabilizer representation of its orbit. -/
def inductionSupportOrbitIso (hP : IsClosed (P : Set G)) (hQ : IsClosed (Q : Set G))
    {m : ℕ} (s : Geometric.OrderedDoubleCosets P Q m) (i : Fin m) :
    (inductionSupportFiltration.{uG, uV} dP hU s).graded i ≅
      smoothParabolicInducingFunctor dP hU hp ⋙
        Geometric.orbitPiece P Q (s.representative i) := by
  let e := Classical.choice (Geometric.closedSubgroupMackeyFiltration.{uG, uV} G
    P Q hP hQ m s i)
  exact (inductionSupportCompactIso dP hU hp s i).symm ≪≫
    Functor.isoWhiskerLeft (smoothParabolicInducingFunctor dP hU hp) e

variable (dQ : IsSemidirectDecomposition Q L V) (hV : IsClosed (V : Set G))

set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 800000 in
/-- The Jacquet support grade is the normalized `V`-coinvariant functor of the
compact stabilizer orbit piece. -/
def jacquetSupportOrbitIso (hP : IsClosed (P : Set G)) (hQ : IsClosed (Q : Set G))
    (hVc : Jacquet.Localization.IsLimitOfCompactSubgroups (V.subgroupOf Q))
    {m : ℕ} (s : Geometric.OrderedDoubleCosets P Q m) (i : Fin m) :
    (jacquetSupportFiltration.{uG, uV} dP hU dQ hV s).graded i ≅
      smoothParabolicInducingFunctor dP hU hp ⋙
        Geometric.orbitPiece P Q (s.representative i) ⋙
          parabolicCoinvariantsFunctor dQ hV :=
  jacquetSupportGradedIso dP hU dQ hV hVc s i ≪≫
    Functor.isoWhiskerRight (inductionSupportOrbitIso dP hU hp hP hQ s i)
      (parabolicCoinvariantsFunctor dQ hV) ≪≫
    Functor.associator _ _ _

end Orbit

end Generic

end Langlands.Aubert.General
