import Langlands.Cohomology.DivisibleSystem.TwistedTruncation
import Langlands.Cohomology.DivisibleSystem.ConstantInverseLimit

/-!
# Harris's complexes `C_m^•`, (2.6), (2.7) and Lemma 2.8 on a twisted site

Harris replaces the finite-length complexes `G^•_m(U(ẽ)_F̄)` of (2.3) by complexes `C^•_m` of
projective modules: he takes invariants under shrinking open normal pro-`p` subgroups `H`,
resolves them by the standard resolutions over the finite groups `S(ẽ)/H` and passes to the
direct limit over `H`. Then (2.6) `C^•_m ⟶ G^•_m(U(ẽ)_F̄)` is a quasi-isomorphism, (2.7) computes
`H^q_c(U(ẽ)_F̄, ℤ/ℓ^m)` as `H^q(C^•_m)`, and Lemma 2.8 identifies the cohomology of
`lim_m C^•_m` with `lim_m H^q_c`.

This module applies the published generic constructions of the `DivisibleSystem` series to the
twisted-site system `Γ_c(G^•_m)` of `DivisibleSystem.TwistedTruncation`. It first proves that
Harris's (2.3) isomorphism is natural in `m`, for the generic acyclic truncation, so that the
limit over `m` of the cohomologies of `Γ_c(G^•_m)` is the limit of the compactly supported
cohomologies `H^n_c(T m)`.
-/

noncomputable section

namespace Langlands.Cohomology

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u uG uI v' u'

namespace DivisibleSystem

section Naturality

variable {C : Type u} [Category.{v} C] [Abelian C] {ℓ : ℕ}
variable (F : C ⥤ C) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  (η : 𝟭 C ⟶ F) [∀ X : C, Mono (η.app X)] (T : DivisibleSystem C ℓ) (D : ℕ)

/-- The augmentations `T m ⟶ F^•_m` of the resolution system commute with the transition
maps. -/
lemma resolutionSystemAugmentation_naturality {m m' : ℕ} (f : op m ⟶ op m') :
    (CochainComplex.single₀ C).map (T.tower.map f) ≫ T.resolutionSystemAugmentation F η m' =
      T.resolutionSystemAugmentation F η m ≫ (T.resolutionSystem F η).tower.map f := by
  apply HomologicalComplex.from_single_hom_ext
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, CochainComplex.single₀_map_f_zero,
    resolutionSystemAugmentation_f_zero, resolutionSystemAugmentation_f_zero]
  exact (T.residualInclusion F η 0).tower.naturality f

/-- The augmentations `T m ⟶ G^•_m` of the truncated resolution system commute with the
transition maps. -/
lemma truncatedResolutionAugmentation_naturality {m m' : ℕ} (f : op m ⟶ op m') :
    (CochainComplex.single₀ C).map (T.tower.map f) ≫ T.truncatedResolutionAugmentation F η D m' =
      T.truncatedResolutionAugmentation F η D m ≫
        (T.truncatedResolutionSystem F η D).tower.map f := by
  apply HomologicalComplex.from_single_hom_ext
  rw [← cancel_mono (((T.truncatedResolutionHom F η D).tower.app (op m')).f 0)]
  have h := congrArg (fun φ => HomologicalComplex.Hom.f φ 0)
    (T.resolutionSystemAugmentation_naturality F η f)
  have h2 := (T.truncatedResolutionHom F η D).tower.naturality f
  simp only [← HomologicalComplex.comp_f, Category.assoc, truncatedResolutionAugmentation_comp]
  rw [h2, truncatedResolutionAugmentation_comp_assoc]
  exact h

end Naturality

section AcyclicNaturality

variable {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C] {ℓ : ℕ}
  {E : Type u'} [Category.{v'} E] [Abelian E] (Φ : C ⥤ E) [Φ.Additive] [PreservesFiniteLimits Φ]
variable (F : C ⥤ C) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  (η : 𝟭 C ⟶ F) [∀ X : C, Mono (η.app X)] (T : DivisibleSystem C ℓ) (D : ℕ)
  (hF : ∀ (M : C) (r : ℕ), IsZero ((Φ.rightDerived (r + 1)).obj (F.obj M)))
  (hT : ∀ (m n : ℕ), D < n → IsZero ((Φ.rightDerived n).obj (T.obj m)))

/-- Harris (2.3), naturally in `m`: the cohomology of the section complexes `Φ(G^•_m)` is the
right derived functor `Rⁿ Φ(T m)`, as functors of `m`. -/
def acyclicTruncatedSectionsHomologyNatIso (n : ℕ) :
    (acyclicTruncatedSectionsSystem Φ F η T D hF hT).tower ⋙
        HomologicalComplex.homologyFunctor E (ComplexShape.up ℕ) n ≅
      T.tower ⋙ Φ.rightDerived n :=
  NatIso.ofComponents (fun m => acyclicTruncatedSectionsHomologyIso Φ F η T D hF hT m.unop n)
    (by
      rintro ⟨m⟩ ⟨m'⟩ f
      exact AcyclicResolution.resolutionComparison_naturality Φ
        (T.truncatedResolutionAugmentation F η D m) (T.truncatedResolutionAugmentation F η D m')
        (T.tower.map f) ((T.truncatedResolutionSystem F η D).tower.map f)
        (T.truncatedResolutionAugmentation_naturality F η D f).symm n)

lemma acyclicTruncatedSectionsHomologyNatIso_app (n m : ℕ) :
    (acyclicTruncatedSectionsHomologyNatIso Φ F η T D hF hT n).app (op m) =
      acyclicTruncatedSectionsHomologyIso Φ F η T D hF hT m n :=
  rfl

end AcyclicNaturality

section Twisted

open Langlands.Sheaf.Equivariant Langlands.Sheaf.Equivariant.TwistedOver

variable {C : Type u} [Category.{v} C] {P : MorphismProperty C} [P.RespectsIso] {X : C}
variable {G : Type uG} [Group G] (ρ : G →* Aut X)
variable (J : GrothendieckTopology (P.Over ⊤ X)) [IsTranslationInvariant (ρ := ρ) J]
variable [TopologicalSpace G] (L : LocalActionSystem (TwistedOver P ρ) G)
variable {I : Type (max w uG)} (points : I → GrothendieckTopology.Point.{max w uG} J)
variable (R : Type (max w uG)) [CommRing R]
variable [∀ F : (P.Over ⊤ X)ᵒᵖ ⥤ ModuleCat.{max w uG} R,
  (ι P ρ).op.HasPointwiseRightKanExtension F]
variable [L.HasFiniteEquivariantRefinements (twistedTopology ρ J)]
variable [HasSheafify (twistedTopology ρ J) (ModuleCat.{max w uG} R)]
variable [PreservesFiniteLimits (discreteZeroFunctor ρ J L points R)]
  [PreservesFiniteColimits (discreteZeroFunctor ρ J L points R)]
variable {ℓ : ℕ}
  (T : DivisibleSystem (L.DiscreteSheaf (ModuleCat.{max w uG} R) (twistedTopology ρ J)) ℓ)
variable (hpoints : JointlyFaithful (fun i => (points i).sheafFiber (A := ModuleCat.{max w uG} R)))
variable (D : ℕ)
variable [P.ContainsIdentities] [LocallySmall.{max w uG} (P.Over ⊤ X)] [IsTopologicalGroup G]
variable [HasSheafify J (ModuleCat.{max w uG} R)]
variable [EnoughInjectives (Sheaf (twistedTopology ρ J) (ModuleCat.{max w uG} R))]
variable {I' : Type uI} [MulAction G I'] [TopologicalSpace I'] [ContinuousConstSMul G I']
  {Ψ : I' → J.Point.{max w uG}} (E : PointEquivariance ρ Ψ)
variable (hF : ∀ (M : L.DiscreteSheaf (ModuleCat.{max w uG} R) (twistedTopology ρ J)) (r : ℕ),
    IsZero ((discreteCompactDerived J R L E (r + 1)).obj
      ((discreteZeroFunctor ρ J L points R).obj M)))
  (hT : ∀ m n : ℕ, D < n → IsZero ((discreteCompactDerived J R L E n).obj (T.obj m)))

/-- Every level of the compact section complexes `Γ_c(G^•_m)` vanishes in degrees `q ≥ D + 2`. -/
theorem isZero_discreteGodementTruncatedCompactSectionsSystem_obj_X (m q : ℕ) (hq : D + 2 ≤ q) :
    IsZero (((discreteGodementTruncatedCompactSectionsSystem ρ J L points R T hpoints D E hF
      hT).obj m).X q) :=
  (discreteCompactSections J R L E).map_isZero
    (isZero_discreteGodementTruncatedResolutionSystem_obj_X ρ J L points R T hpoints D m
      (by omega))

/-- Harris (2.3) on the twisted site, naturally in `m`. -/
def discreteGodementTruncatedCompactHomologyNatIso (n : ℕ) :
    (discreteGodementTruncatedCompactSectionsSystem ρ J L points R T hpoints D E hF hT).tower ⋙
        HomologicalComplex.homologyFunctor _ (ComplexShape.up ℕ) n ≅
      T.tower ⋙ discreteCompactDerived J R L E n :=
  haveI := discreteZeroFunctor_additive ρ J L points R
  haveI := mono_discreteCoaugmentation_of_jointlyFaithful ρ J L points R hpoints
  acyclicTruncatedSectionsHomologyNatIso (discreteCompactSections J R L E)
    (discreteZeroFunctor ρ J L points R) (discreteCoaugmentation ρ J L points R) T D hF hT n

/-- The cohomology of level `m` of `Γ_c(G^•)`, viewed in representations, is `H^n_c(T m)`. -/
def discreteGodementTruncatedCompactRepHomologyIso (m n : ℕ) :
    ((discreteGodementTruncatedCompactSectionsSystem ρ J L points R T hpoints D E hF
      hT).toRepComplexes.obj m).homology n ≅
      SmoothRep.toRep.obj ((discreteCompactDerived J R L E n).obj (T.obj m)) :=
  (mapHomologicalComplexHomologyIso SmoothRep.toRep (ComplexShape.up ℕ) n).app
      ((discreteGodementTruncatedCompactSectionsSystem ρ J L points R T hpoints D E hF hT).obj m) ≪≫
    SmoothRep.toRep.mapIso
      (discreteGodementTruncatedCompactHomologyIso ρ J L points R T hpoints D E hF hT m n)

/-- If `H i` acts trivially on `H^q_c(T m)` for every `q`, it acts trivially on the cohomology of
level `m` of `Γ_c(G^•)`. -/
lemma discreteGodementTruncatedCompactRepHomology_ρ_eq_id {m : ℕ} {K' : Subgroup G}
    (htriv : ∀ q (g : K'),
      (SmoothRep.toRep.obj ((discreteCompactDerived J R L E q).obj (T.obj m))).ρ g =
        LinearMap.id) (q : ℕ) (g : K') :
    (((discreteGodementTruncatedCompactSectionsSystem ρ J L points R T hpoints D E hF
      hT).toRepComplexes.obj m).homology q).ρ g = LinearMap.id :=
  Rep.ρ_eq_id_of_iso
    (discreteGodementTruncatedCompactRepHomologyIso.{w, v, u, uG, uI} ρ J L points R T hpoints D E
      hF hT m q).symm
    (htriv q g)

variable {ι : Type uG} [Preorder ι] (H : ι → Subgroup G) (hH : Antitone H)
  [∀ i, (H i).Normal] [∀ i, (H i).FiniteIndex] [∀ i, Fintype (G ⧸ H i)]
  [∀ i, DecidableEq (G ⧸ H i)]
  (hK : ∀ i {m' m : ℕ} (h : m' ≤ m) (q : ℕ),
    Epi ((smoothQuotientInvariants R (H i)).map
      (((discreteGodementTruncatedCompactSectionsSystem ρ J L points R T hpoints D E hF
        hT).projection h).f q)))
  (hk : ∀ {i j : ι} (hij : i ≤ j), IsUnit (Nat.card (quotientProjection (hH hij)).ker : R))
  [IsFiltered ι]

/-- Harris's `C^•_m` on the twisted site: the direct limit over `i` of the inflated complexes
`C^{•,H i}_m` built from the `H i`-invariants of `Γ_c(G^•_m)` (rows `q < D + 2`). -/
abbrev discreteGodementQuotientInvariantsLimit :
    DivisibleSystem (CochainComplex (Rep.{max w uG} R G) ℤ) ℓ :=
  quotientInvariantsLimit.{w, max w uG, uG} (D + 2)
    (discreteGodementTruncatedCompactSectionsSystem ρ J L points R T hpoints D E hF hT) H hH hK hk

/-- Harris's comparison (2.6) `C^•_m ⟶ Γ_c(G^•_m)` on the twisted site. -/
abbrev discreteGodementQuotientInvariantsLimitToRepExtend :
    discreteGodementQuotientInvariantsLimit.{w, v, u, uG, uI} ρ J L points R T hpoints D E hF hT H
      hH hK hk ⟶
      (discreteGodementTruncatedCompactSectionsSystem ρ J L points R T hpoints D E hF
        hT).toRepComplexes.extendSystem :=
  quotientInvariantsLimitToRepExtend.{w, max w uG, uG} (D + 2)
    (discreteGodementTruncatedCompactSectionsSystem ρ J L points R T hpoints D E hF hT) H hH hK hk
    (isZero_discreteGodementTruncatedCompactSectionsSystem_obj_X.{w, v, u, uG, uI} ρ J L points R T
      hpoints D E hF
      hT)

/-- Harris (2.6) on the twisted site: given `ProPInvariantSubcomplexStatement`, if every `H i` is
a normal pro-`p` subgroup, `p` is invertible in `R` and every `H i` acts trivially on the
compactly supported cohomology of `T m`, the comparison is a quasi-isomorphism at level `m`. -/
theorem quasiIso_discreteGodementQuotientInvariantsLimitToRepExtend
    (hS : ProPInvariantSubcomplexStatement.{uG, max w uG, max w uG}) {p : ℕ}
    (hP : ∀ i, IsProPSubgroup p (H i)) (hR : IsUnit (p : R)) (m : ℕ)
    (htriv : ∀ i q (g : H i),
      (SmoothRep.toRep.obj ((discreteCompactDerived J R L E q).obj (T.obj m))).ρ g =
        LinearMap.id) :
    QuasiIso ((discreteGodementQuotientInvariantsLimitToRepExtend.{w, v, u, uG, uI} ρ J L points R
      T hpoints D E hF
      hT H hH hK hk).tower.app (op m)) :=
  quasiIso_quotientInvariantsLimitToRepExtend.{w, max w uG, uG} (D + 2) _ H hH hK hk hS hP hR
    (isZero_discreteGodementTruncatedCompactSectionsSystem_obj_X.{w, v, u, uG, uI} ρ J L points R T
      hpoints D E hF
      hT) m
    (fun i => discreteGodementTruncatedCompactRepHomology_ρ_eq_id.{w, v, u, uG, uI} ρ J L points R
      T hpoints D E
      hF hT (htriv i))

/-- Harris (2.7) on the twisted site: under the hypotheses of
`quasiIso_discreteGodementQuotientInvariantsLimitToRepExtend`, the cohomology of `C^•_m` is the
compactly supported cohomology `H^n_c(T m)`. -/
def discreteGodementQuotientInvariantsLimitHomologyIso
    (hS : ProPInvariantSubcomplexStatement.{uG, max w uG, max w uG}) {p : ℕ}
    (hP : ∀ i, IsProPSubgroup p (H i)) (hR : IsUnit (p : R)) (m : ℕ)
    (htriv : ∀ i q (g : H i),
      (SmoothRep.toRep.obj ((discreteCompactDerived J R L E q).obj (T.obj m))).ρ g =
        LinearMap.id) (n : ℕ) :
    ((discreteGodementQuotientInvariantsLimit.{w, v, u, uG, uI} ρ J L points R T hpoints D E hF hT
      H hH hK
      hk).obj m).homology n ≅
      SmoothRep.toRep.obj ((discreteCompactDerived J R L E n).obj (T.obj m)) :=
  haveI := quasiIso_discreteGodementQuotientInvariantsLimitToRepExtend.{w, v, u, uG, uI} ρ J L
    points R T hpoints D
    E hF hT H hH hK hk hS hP hR m htriv
  isoOfQuasiIsoAt ((discreteGodementQuotientInvariantsLimitToRepExtend.{w, v, u, uG, uI} ρ J L
    points R T hpoints
      D E hF hT H hH hK hk).tower.app (op m)) n ≪≫
    (extendHomologyNatIso _ n).app ((discreteGodementTruncatedCompactSectionsSystem ρ J L points
      R T hpoints D E hF hT).toRepComplexes.obj m) ≪≫
    discreteGodementTruncatedCompactRepHomologyIso.{w, v, u, uG, uI} ρ J L points R T hpoints D E
      hF hT m n

/-- Harris's `lim_m C^•_m` on the twisted site. -/
abbrev discreteGodementQuotientInvariantsInverseLimit : CochainComplex (Rep.{max w uG} R G) ℤ :=
  quotientInvariantsInverseLimit.{w, max w uG, uG} (D + 2)
    (discreteGodementTruncatedCompactSectionsSystem ρ J L points R T hpoints D E hF hT) H hH hK hk

/-- Harris's Lemma 2.8 on the twisted site: given `ProPInvariantSubcomplexStatement` and
`FiniteCohomologyInverseLimitStatement`, if every `H i` is a normal pro-`p` subgroup, `p` is
invertible in `R`, and the compactly supported cohomology of every level of `T` is finite with
trivial action of every `H i`, then the degree-`n` cohomology of `lim_m C^•_m` is the inverse
limit over `m` of `H^n_c(T m)`. -/
def discreteGodementQuotientInvariantsInverseLimitHomologyIso
    (hS : ProPInvariantSubcomplexStatement.{uG, max w uG, max w uG})
    (hS' : FiniteCohomologyInverseLimitStatement.{max w uG, max w uG} R) {p : ℕ}
    (hP : ∀ i, IsProPSubgroup p (H i)) (hR : IsUnit (p : R))
    (htriv : ∀ m i q (g : H i),
      (SmoothRep.toRep.obj ((discreteCompactDerived J R L E q).obj (T.obj m))).ρ g =
        LinearMap.id)
    (hfin : ∀ m q,
      Finite (SmoothRep.toRep.obj ((discreteCompactDerived J R L E q).obj (T.obj m))))
    (n : ℕ) :
    (discreteGodementQuotientInvariantsInverseLimit.{w, v, u, uG, uI} ρ J L points R T hpoints D E
      hF hT H hH hK
      hk).homology n ≅
      limit (T.tower ⋙ discreteCompactDerived J R L E n ⋙ SmoothRep.toRep) :=
  haveI := isIso_quotientInvariantsInverseLimitComparison.{w, max w uG, uG} (D + 2)
    (discreteGodementTruncatedCompactSectionsSystem ρ J L points R T hpoints D E hF hT) H hH hK hk
    hS hS' hP hR
    (isZero_discreteGodementTruncatedCompactSectionsSystem_obj_X.{w, v, u, uG, uI} ρ J L points R T
      hpoints D E hF
      hT)
    (fun m i => discreteGodementTruncatedCompactRepHomology_ρ_eq_id.{w, v, u, uG, uI} ρ J L points
      R T hpoints D E
      hF hT (htriv m i))
    (fun m q => finite_of_rep_iso
      (discreteGodementTruncatedCompactRepHomologyIso.{w, v, u, uG, uI} ρ J L points R T hpoints D
        E hF hT m q).symm
      (hfin m q)) n
  asIso (quotientInvariantsInverseLimitComparison.{w, max w uG, uG} (D + 2)
      (discreteGodementTruncatedCompactSectionsSystem ρ J L points R T hpoints D E hF hT) H hH hK
      hk (isZero_discreteGodementTruncatedCompactSectionsSystem_obj_X.{w, v, u, uG, uI} ρ J L
        points R T hpoints D E
        hF hT) n) ≪≫
    (discreteGodementTruncatedCompactSectionsSystem ρ J L points R T hpoints D E hF
      hT).toRepComplexes.extendLevelCohomologyLimitIso n ≪≫
    lim.mapIso (Functor.isoWhiskerLeft
      (discreteGodementTruncatedCompactSectionsSystem ρ J L points R T hpoints D E hF hT).tower
      (mapHomologicalComplexHomologyIso SmoothRep.toRep (ComplexShape.up ℕ) n)) ≪≫
    lim.mapIso (Functor.isoWhiskerRight
      (discreteGodementTruncatedCompactHomologyNatIso.{w, v, u, uG, uI} ρ J L points R T hpoints D
        E hF hT n)
      SmoothRep.toRep)

end Twisted

end DivisibleSystem

end Langlands.Cohomology
