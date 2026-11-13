import Langlands.Sheaf.Equivariant.TwistedExactGodement
import Langlands.Sheaf.Equivariant.TwistedExactCompactComparison
import Langlands.Cohomology.DivisibleSystem.TwistedInverseLimit

/-!
# Harris's `ℓ`-divisible Godement systems on a coreflective subcategory of twisted sheaves

The published modules `DivisibleSystem.TwistedGodement`, `DivisibleSystem.TwistedTruncation`
and `DivisibleSystem.TwistedInverseLimit` construct Harris's Lemma 2.2, Lemma 2.2 bis, (2.3),
(2.6), (2.7) and Lemma 2.8 for the discrete sheaves of a local action system on a twisted site.
This module repeats these constructions for an abelian category `𝒜` with a fully faithful
functor `incl` into module sheaves on the twisted site and a right adjoint `cor`: the
Godement functor is `exactZeroFunctor` of `TwistedExactGodement`, and compactly supported
cohomology is `exactCompactDerived` of `TwistedExactCompactComparison`. The locally discrete
sheaves of `LocalActionSmoothPart`, which model Berkovich's étale `G`-sheaves, are an
instance.

As in the published modules, the exactness of the Godement functor (Harris's Fact 3), the
joint faithfulness of the fibers at the points, the acyclicity of Godement sheaves for
compactly supported sections and the bound `D` on compactly supported cohomology (Fact 2)
are hypotheses.
-/

noncomputable section

namespace Langlands.Cohomology.DivisibleSystem

open CategoryTheory CategoryTheory.Limits Opposite
open Langlands.Sheaf.Equivariant Langlands.Sheaf.Equivariant.TwistedOver

universe w v u uG uI uA vA

section Godement

variable {C : Type u} [Category.{v} C] {P : MorphismProperty C} [P.RespectsIso] {X : C}
variable {G : Type uG} [Group G] (ρ : G →* Aut X)
variable (J : GrothendieckTopology (P.Over ⊤ X)) [IsTranslationInvariant (ρ := ρ) J]
variable {I : Type w} (points : I → GrothendieckTopology.Point.{w} J)
variable (R : Type w) [CommRing R]
variable [∀ F : (P.Over ⊤ X)ᵒᵖ ⥤ ModuleCat.{w} R, (ι P ρ).op.HasPointwiseRightKanExtension F]
variable {𝒜 : Type uA} [Category.{vA} 𝒜] [Abelian 𝒜]
variable {incl : 𝒜 ⥤ Sheaf (twistedTopology ρ J) (ModuleCat.{w} R)}
variable {cor : Sheaf (twistedTopology ρ J) (ModuleCat.{w} R) ⥤ 𝒜} (adj : incl ⊣ cor)
variable [PreservesFiniteLimits (exactZeroFunctor ρ J points R incl cor)]

section LeftExact

attribute [local instance] preservesBinaryBiproducts_of_preservesBinaryProducts in
/-- A left exact Godement functor on `𝒜` is additive. -/
theorem exactZeroFunctor_additive : (exactZeroFunctor ρ J points R incl cor).Additive :=
  Functor.additive_of_preservesBinaryBiproducts _

end LeftExact

variable [PreservesFiniteColimits (exactZeroFunctor ρ J points R incl cor)]
variable {ℓ : ℕ} (T : DivisibleSystem 𝒜 ℓ)

section Exact

/-- Harris's Fact 4 on `𝒜`: the images `F(T_m)` under the exact Godement functor form an
`ℓ`-divisible system. -/
def exactGodementImageSystem : DivisibleSystem 𝒜 ℓ :=
  haveI := exactZeroFunctor_additive ρ J points R (incl := incl) (cor := cor)
  T.map (exactZeroFunctor ρ J points R incl cor)

/-- The embeddings `b_m : T_m ⟶ F(T_m)` as a morphism of `ℓ`-divisible systems. -/
def exactGodementCoaugmentation :
    T ⟶ exactGodementImageSystem ρ J points R (incl := incl) (cor := cor) T :=
  haveI := exactZeroFunctor_additive ρ J points R (incl := incl) (cor := cor)
  T.coaugmentation (exactZeroFunctor ρ J points R incl cor) (exactCoaugmentation ρ J points R adj)

variable [incl.Full] [incl.Faithful]
variable (hpoints : JointlyFaithful (fun i => (points i).sheafFiber (A := ModuleCat.{w} R)))

/-- The residual systems: `T` in degree `0`, and in degree `q + 1` the cokernel system of the
coaugmentation of the residual system in degree `q`. -/
def exactGodementResidualSystem (q : ℕ) : DivisibleSystem 𝒜 ℓ :=
  haveI := exactZeroFunctor_additive ρ J points R (incl := incl) (cor := cor)
  haveI := mono_exactCoaugmentation_of_jointlyFaithful ρ J points R adj hpoints
  T.residualSystem (exactZeroFunctor ρ J points R incl cor) (exactCoaugmentation ρ J points R adj) q

/-- The term systems `F^q`: the Godement functor applied to the residual system in degree
`q`. -/
def exactGodementTermSystem (q : ℕ) : DivisibleSystem 𝒜 ℓ :=
  haveI := exactZeroFunctor_additive ρ J points R (incl := incl) (cor := cor)
  haveI := mono_exactCoaugmentation_of_jointlyFaithful ρ J points R adj hpoints
  T.termSystem (exactZeroFunctor ρ J points R incl cor) (exactCoaugmentation ρ J points R adj) q

/-- Harris's Lemma 2.2 on `𝒜`: the `ℓ`-divisible system of the Godement resolutions
`F^0 ⟶ F^1 ⟶ ⋯` of the levels of `T`. -/
def exactGodementResolutionSystem : DivisibleSystem (CochainComplex 𝒜 ℕ) ℓ :=
  haveI := exactZeroFunctor_additive ρ J points R (incl := incl) (cor := cor)
  haveI := mono_exactCoaugmentation_of_jointlyFaithful ρ J points R adj hpoints
  resolutionSystem (exactZeroFunctor ρ J points R incl cor) (exactCoaugmentation ρ J points R adj) T

/-- Degree `q` of the resolution system is the term system `F^q`. -/
def exactGodementResolutionSystemDegreeIso (q : ℕ) :
    (exactGodementResolutionSystem ρ J points R adj T hpoints).degree q ≅
      exactGodementTermSystem ρ J points R adj T hpoints q :=
  haveI := exactZeroFunctor_additive ρ J points R (incl := incl) (cor := cor)
  haveI := mono_exactCoaugmentation_of_jointlyFaithful ρ J points R adj hpoints
  resolutionSystemDegreeIso (exactZeroFunctor ρ J points R incl cor)
    (exactCoaugmentation ρ J points R adj) T q

/-- Level `m` of the resolution system is the Godement complex `exactComplexFunctor` of
`T_m`. -/
def exactGodementResolutionSystemObjIso (m : ℕ) :
    (exactGodementResolutionSystem ρ J points R adj T hpoints).obj m ≅
      (exactComplexFunctor ρ J points R adj).obj (T.obj m) :=
  haveI := exactZeroFunctor_additive ρ J points R (incl := incl) (cor := cor)
  haveI := mono_exactCoaugmentation_of_jointlyFaithful ρ J points R adj hpoints
  resolutionSystemObjIso (exactZeroFunctor ρ J points R incl cor)
    (exactCoaugmentation ρ J points R adj) T m

/-- Every level of the resolution system is exact in positive degrees. -/
theorem exactGodementResolutionSystem_obj_exactAt (m q : ℕ) :
    ((exactGodementResolutionSystem ρ J points R adj T hpoints).obj m).ExactAt (q + 1) :=
  haveI := exactZeroFunctor_additive ρ J points R (incl := incl) (cor := cor)
  haveI := mono_exactCoaugmentation_of_jointlyFaithful ρ J points R adj hpoints
  resolutionSystem_obj_exactAt (exactZeroFunctor ρ J points R incl cor)
    (exactCoaugmentation ρ J points R adj) T m q

end Exact

variable [incl.Full] [incl.Faithful]
variable (hpoints : JointlyFaithful (fun i => (points i).sheafFiber (A := ModuleCat.{w} R)))
variable (D : ℕ)

section Truncation

/-- Harris's truncation `G^• = τ_{≤ D+1}(F^•)` of the Godement resolution system: the term
systems `F^q` for `q ≤ D`, the residual system in degree `D + 1`, and zero above. -/
def exactGodementTruncatedResolutionSystem : DivisibleSystem (CochainComplex 𝒜 ℕ) ℓ :=
  haveI := exactZeroFunctor_additive ρ J points R (incl := incl) (cor := cor)
  haveI := mono_exactCoaugmentation_of_jointlyFaithful ρ J points R adj hpoints
  T.truncatedResolutionSystem (exactZeroFunctor ρ J points R incl cor)
    (exactCoaugmentation ρ J points R adj) D

/-- The inclusion `G^• ⟶ F^•` of the truncation into the Godement resolution system. -/
def exactGodementTruncatedResolutionHom :
    exactGodementTruncatedResolutionSystem ρ J points R adj T hpoints D ⟶
      exactGodementResolutionSystem ρ J points R adj T hpoints :=
  haveI := exactZeroFunctor_additive ρ J points R (incl := incl) (cor := cor)
  haveI := mono_exactCoaugmentation_of_jointlyFaithful ρ J points R adj hpoints
  T.truncatedResolutionHom (exactZeroFunctor ρ J points R incl cor)
    (exactCoaugmentation ρ J points R adj) D

/-- At every level, the inclusion of the truncation is a quasi-isomorphism. -/
theorem quasiIso_exactGodementTruncatedResolutionHom (m : ℕ) :
    QuasiIso ((exactGodementTruncatedResolutionHom ρ J points R adj T hpoints D).tower.app
      (op m)) :=
  haveI := exactZeroFunctor_additive ρ J points R (incl := incl) (cor := cor)
  haveI := mono_exactCoaugmentation_of_jointlyFaithful ρ J points R adj hpoints
  truncatedResolutionHom_quasiIso (exactZeroFunctor ρ J points R incl cor)
    (exactCoaugmentation ρ J points R adj) T D m

/-- Every level of the truncation is zero in degrees above `D + 1`. -/
theorem isZero_exactGodementTruncatedResolutionSystem_obj_X (m : ℕ) {q : ℕ} (hq : D + 1 < q) :
    IsZero (((exactGodementTruncatedResolutionSystem ρ J points R adj T hpoints D).obj m).X q) :=
  haveI := exactZeroFunctor_additive ρ J points R (incl := incl) (cor := cor)
  haveI := mono_exactCoaugmentation_of_jointlyFaithful ρ J points R adj hpoints
  T.isZero_truncatedResolutionSystem_obj_X (exactZeroFunctor ρ J points R incl cor)
    (exactCoaugmentation ρ J points R adj) D m hq

/-- The augmentation `T m ⟶ G^•_m`. -/
def exactGodementTruncatedAugmentation (m : ℕ) :
    (CochainComplex.single₀ _).obj (T.obj m) ⟶
      (exactGodementTruncatedResolutionSystem ρ J points R adj T hpoints D).obj m :=
  haveI := exactZeroFunctor_additive ρ J points R (incl := incl) (cor := cor)
  haveI := mono_exactCoaugmentation_of_jointlyFaithful ρ J points R adj hpoints
  T.truncatedResolutionAugmentation (exactZeroFunctor ρ J points R incl cor)
    (exactCoaugmentation ρ J points R adj) D m

/-- Each level of the truncation is a finite-length resolution of the level of `T`. -/
theorem quasiIso_exactGodementTruncatedAugmentation (m : ℕ) :
    QuasiIso (exactGodementTruncatedAugmentation ρ J points R adj T hpoints D m) :=
  haveI := exactZeroFunctor_additive ρ J points R (incl := incl) (cor := cor)
  haveI := mono_exactCoaugmentation_of_jointlyFaithful ρ J points R adj hpoints
  truncatedResolutionAugmentation_quasiIso (exactZeroFunctor ρ J points R incl cor)
    (exactCoaugmentation ρ J points R adj) T D m

end Truncation

section Compact

variable [P.ContainsIdentities] [LocallySmall.{w} (P.Over ⊤ X)]
variable [TopologicalSpace G] [IsTopologicalGroup G]
variable [HasSheafify J (ModuleCat.{w} R)] [incl.Additive]
variable [PreservesFiniteLimits incl] [PreservesFiniteColimits incl] [EnoughInjectives 𝒜]
variable {I' : Type uI} [MulAction G I'] [TopologicalSpace I'] [ContinuousConstSMul G I']
  {Ψ : I' → J.Point.{w}} (E : PointEquivariance ρ Ψ)
variable (hF : ∀ (M : 𝒜) (r : ℕ),
    IsZero ((exactCompactDerived J R incl E (r + 1)).obj
      ((exactZeroFunctor ρ J points R incl cor).obj M)))
  (hT : ∀ m n : ℕ, D < n → IsZero ((exactCompactDerived J R incl E n).obj (T.obj m)))

omit [HasSheafify J (ModuleCat.{w} R)] [PreservesFiniteLimits incl]
  [PreservesFiniteColimits incl] in
include hF hT in
/-- Every term of every level of the truncation is acyclic for smooth compactly supported
sections. -/
theorem isZero_exactCompactDerived_truncatedResolutionSystem_obj_X (m i r : ℕ) :
    IsZero ((exactCompactDerived J R incl E (r + 1)).obj
      (((exactGodementTruncatedResolutionSystem ρ J points R adj T hpoints D).obj m).X i)) :=
  haveI := exactZeroFunctor_additive ρ J points R (incl := incl) (cor := cor)
  haveI := mono_exactCoaugmentation_of_jointlyFaithful ρ J points R adj hpoints
  isZero_rightDerived_truncatedResolutionSystem_obj_X (exactCompactSections J R incl E)
    (exactZeroFunctor ρ J points R incl cor) (exactCoaugmentation ρ J points R adj) T D hF hT
    m i r

/-- Harris's `ℓ`-divisible system of finite-length complexes `Γ_c(G^•_m)` of smooth
representations, on `𝒜`. -/
def exactGodementTruncatedCompactSectionsSystem :
    DivisibleSystem (CochainComplex (SmoothRep.{w, uG, w} R G) ℕ) ℓ :=
  haveI := exactZeroFunctor_additive ρ J points R (incl := incl) (cor := cor)
  haveI := mono_exactCoaugmentation_of_jointlyFaithful ρ J points R adj hpoints
  acyclicTruncatedSectionsSystem (exactCompactSections J R incl E)
    (exactZeroFunctor ρ J points R incl cor) (exactCoaugmentation ρ J points R adj) T D hF hT

omit [PreservesFiniteColimits incl] in
/-- Level `m` of the section system is the complex of smooth compactly supported sections of
`G^•_m`. -/
theorem exactGodementTruncatedCompactSectionsSystem_obj (m : ℕ) :
    (exactGodementTruncatedCompactSectionsSystem ρ J points R adj T hpoints D E hF hT).obj m =
      ((exactCompactSections J R incl E).mapHomologicalComplex _).obj
        ((exactGodementTruncatedResolutionSystem ρ J points R adj T hpoints D).obj m) :=
  rfl

/-- Harris (2.3) on `𝒜`: the cohomology of level `m` of the compact section complexes is the
compactly supported cohomology `H^n_c` of `T m`. -/
def exactGodementTruncatedCompactHomologyIso (m n : ℕ) :
    ((exactGodementTruncatedCompactSectionsSystem ρ J points R adj T hpoints D E hF hT).obj
      m).homology n ≅ (exactCompactDerived J R incl E n).obj (T.obj m) :=
  haveI := exactZeroFunctor_additive ρ J points R (incl := incl) (cor := cor)
  haveI := mono_exactCoaugmentation_of_jointlyFaithful ρ J points R adj hpoints
  acyclicTruncatedSectionsHomologyIso (exactCompactSections J R incl E)
    (exactZeroFunctor ρ J points R incl cor) (exactCoaugmentation ρ J points R adj) T D hF hT
    m n

omit [PreservesFiniteColimits incl] in
/-- The forward map of `exactGodementTruncatedCompactHomologyIso` is the comparison map of
the acyclic resolution `G^•_m`. -/
theorem exactGodementTruncatedCompactHomologyIso_hom (m n : ℕ) :
    haveI := quasiIso_exactGodementTruncatedAugmentation ρ J points R adj T hpoints D m
    (exactGodementTruncatedCompactHomologyIso ρ J points R adj T hpoints D E hF hT m n).hom =
      AcyclicResolution.resolutionComparison (exactCompactSections J R incl E)
        (exactGodementTruncatedAugmentation ρ J points R adj T hpoints D m) n :=
  rfl

omit [PreservesFiniteColimits incl] in
/-- The cohomology of every level of the compact section complexes vanishes above
degree `D`. -/
theorem isZero_exactGodementTruncatedCompactSectionsSystem_homology (m : ℕ) {n : ℕ}
    (hn : D < n) :
    IsZero (((exactGodementTruncatedCompactSectionsSystem ρ J points R adj T hpoints D E hF
      hT).obj m).homology n) :=
  (hT m n hn).of_iso (exactGodementTruncatedCompactHomologyIso ρ J points R adj T hpoints D E
    hF hT m n)

omit [PreservesFiniteColimits incl] in
/-- Every level of the compact section complexes `Γ_c(G^•_m)` vanishes in degrees
`q ≥ D + 2`. -/
theorem isZero_exactGodementTruncatedCompactSectionsSystem_obj_X (m q : ℕ) (hq : D + 2 ≤ q) :
    IsZero (((exactGodementTruncatedCompactSectionsSystem ρ J points R adj T hpoints D E hF
      hT).obj m).X q) :=
  (exactCompactSections J R incl E).map_isZero
    (isZero_exactGodementTruncatedResolutionSystem_obj_X ρ J points R adj T hpoints D m
      (by omega))

/-- Harris (2.3) on `𝒜`, naturally in `m`. -/
def exactGodementTruncatedCompactHomologyNatIso (n : ℕ) :
    (exactGodementTruncatedCompactSectionsSystem ρ J points R adj T hpoints D E hF hT).tower ⋙
        HomologicalComplex.homologyFunctor _ (ComplexShape.up ℕ) n ≅
      T.tower ⋙ exactCompactDerived J R incl E n :=
  haveI := exactZeroFunctor_additive ρ J points R (incl := incl) (cor := cor)
  haveI := mono_exactCoaugmentation_of_jointlyFaithful ρ J points R adj hpoints
  acyclicTruncatedSectionsHomologyNatIso (exactCompactSections J R incl E)
    (exactZeroFunctor ρ J points R incl cor) (exactCoaugmentation ρ J points R adj) T D hF hT n

/-- The cohomology of level `m` of `Γ_c(G^•)`, viewed in representations, is
`H^n_c(T m)`. -/
def exactGodementTruncatedCompactRepHomologyIso (m n : ℕ) :
    ((exactGodementTruncatedCompactSectionsSystem ρ J points R adj T hpoints D E hF
      hT).toRepComplexes.obj m).homology n ≅
      SmoothRep.toRep.obj ((exactCompactDerived J R incl E n).obj (T.obj m)) :=
  (mapHomologicalComplexHomologyIso SmoothRep.toRep (ComplexShape.up ℕ) n).app
      ((exactGodementTruncatedCompactSectionsSystem ρ J points R adj T hpoints D E hF hT).obj m) ≪≫
    SmoothRep.toRep.mapIso
      (exactGodementTruncatedCompactHomologyIso ρ J points R adj T hpoints D E hF hT m n)

omit [PreservesFiniteColimits incl] in
/-- If a subgroup `K'` acts trivially on `H^q_c(T m)` for every `q`, it acts trivially on the
cohomology of level `m` of `Γ_c(G^•)`. -/
lemma exactGodementTruncatedCompactRepHomology_ρ_eq_id {m : ℕ} {K' : Subgroup G}
    (htriv : ∀ q (g : K'),
      (SmoothRep.toRep.obj ((exactCompactDerived J R incl E q).obj (T.obj m))).ρ g =
        LinearMap.id) (q : ℕ) (g : K') :
    (((exactGodementTruncatedCompactSectionsSystem ρ J points R adj T hpoints D E hF
      hT).toRepComplexes.obj m).homology q).ρ g = LinearMap.id :=
  Rep.ρ_eq_id_of_iso
    (exactGodementTruncatedCompactRepHomologyIso ρ J points R adj T hpoints D E hF hT m q).symm
    (htriv q g)

end Compact

end Godement

section InverseLimit

variable {C : Type u} [Category.{v} C] {P : MorphismProperty C} [P.RespectsIso] {X : C}
variable {G : Type uG} [Group G] (ρ : G →* Aut X)
variable (J : GrothendieckTopology (P.Over ⊤ X)) [IsTranslationInvariant (ρ := ρ) J]
variable {I : Type (max w uG)} (points : I → GrothendieckTopology.Point.{max w uG} J)
variable (R : Type (max w uG)) [CommRing R]
variable [∀ F : (P.Over ⊤ X)ᵒᵖ ⥤ ModuleCat.{max w uG} R,
  (ι P ρ).op.HasPointwiseRightKanExtension F]
variable {𝒜 : Type uA} [Category.{vA} 𝒜] [Abelian 𝒜]
variable {incl : 𝒜 ⥤ Sheaf (twistedTopology ρ J) (ModuleCat.{max w uG} R)}
variable {cor : Sheaf (twistedTopology ρ J) (ModuleCat.{max w uG} R) ⥤ 𝒜} (adj : incl ⊣ cor)
variable [PreservesFiniteLimits (exactZeroFunctor ρ J points R incl cor)]
  [PreservesFiniteColimits (exactZeroFunctor ρ J points R incl cor)]
variable {ℓ : ℕ} (T : DivisibleSystem 𝒜 ℓ)
variable [incl.Full] [incl.Faithful]
variable (hpoints : JointlyFaithful (fun i => (points i).sheafFiber
  (A := ModuleCat.{max w uG} R)))
variable (D : ℕ)
variable [P.ContainsIdentities] [LocallySmall.{max w uG} (P.Over ⊤ X)]
variable [TopologicalSpace G] [IsTopologicalGroup G]
variable [HasSheafify J (ModuleCat.{max w uG} R)] [incl.Additive]
variable [PreservesFiniteLimits incl] [PreservesFiniteColimits incl] [EnoughInjectives 𝒜]
variable {I' : Type uI} [MulAction G I'] [TopologicalSpace I'] [ContinuousConstSMul G I']
  {Ψ : I' → J.Point.{max w uG}} (E : PointEquivariance ρ Ψ)
variable (hF : ∀ (M : 𝒜) (r : ℕ),
    IsZero ((exactCompactDerived J R incl E (r + 1)).obj
      ((exactZeroFunctor ρ J points R incl cor).obj M)))
  (hT : ∀ m n : ℕ, D < n → IsZero ((exactCompactDerived J R incl E n).obj (T.obj m)))
variable {ι : Type uG} [Preorder ι] (H : ι → Subgroup G) (hH : Antitone H)
  [∀ i, (H i).Normal] [∀ i, (H i).FiniteIndex] [∀ i, Fintype (G ⧸ H i)]
  [∀ i, DecidableEq (G ⧸ H i)]
  (hK : ∀ i {m' m : ℕ} (h : m' ≤ m) (q : ℕ),
    Epi ((smoothQuotientInvariants R (H i)).map
      (((exactGodementTruncatedCompactSectionsSystem ρ J points R adj T hpoints D E hF
        hT).projection h).f q)))
  (hk : ∀ {i j : ι} (hij : i ≤ j), IsUnit (Nat.card (quotientProjection (hH hij)).ker : R))
  [IsFiltered ι]

/-- Harris's `C^•_m` on `𝒜`: the direct limit over `i` of the inflated complexes
`C^{•,H i}_m` built from the `H i`-invariants of `Γ_c(G^•_m)` (rows `q < D + 2`). -/
abbrev exactGodementQuotientInvariantsLimit :
    DivisibleSystem (CochainComplex (Rep.{max w uG} R G) ℤ) ℓ :=
  quotientInvariantsLimit.{w, max w uG, uG} (D + 2)
    (exactGodementTruncatedCompactSectionsSystem ρ J points R adj T hpoints D E hF hT) H hH hK hk

/-- Harris's comparison (2.6) `C^•_m ⟶ Γ_c(G^•_m)` on `𝒜`. -/
abbrev exactGodementQuotientInvariantsLimitToRepExtend :
    exactGodementQuotientInvariantsLimit.{w, v, u, uG, uI, uA, vA} ρ J points R adj T hpoints D E
      hF hT H hH hK hk ⟶
      (exactGodementTruncatedCompactSectionsSystem ρ J points R adj T hpoints D E hF
        hT).toRepComplexes.extendSystem :=
  quotientInvariantsLimitToRepExtend.{w, max w uG, uG} (D + 2)
    (exactGodementTruncatedCompactSectionsSystem ρ J points R adj T hpoints D E hF hT) H hH hK hk
    (isZero_exactGodementTruncatedCompactSectionsSystem_obj_X ρ J points R adj T hpoints D E hF
      hT)

omit [PreservesFiniteColimits incl] in
/-- Harris (2.6) on `𝒜`: given `ProPInvariantSubcomplexStatement`, if every `H i` is a normal
pro-`p` subgroup, `p` is invertible in `R` and every `H i` acts trivially on the compactly
supported cohomology of `T m`, the comparison is a quasi-isomorphism at level `m`. -/
theorem quasiIso_exactGodementQuotientInvariantsLimitToRepExtend
    (hS : ProPInvariantSubcomplexStatement.{uG, max w uG, max w uG}) {p : ℕ}
    (hP : ∀ i, IsProPSubgroup p (H i)) (hR : IsUnit (p : R)) (m : ℕ)
    (htriv : ∀ i q (g : H i),
      (SmoothRep.toRep.obj ((exactCompactDerived J R incl E q).obj (T.obj m))).ρ g =
        LinearMap.id) :
    QuasiIso ((exactGodementQuotientInvariantsLimitToRepExtend.{w, v, u, uG, uI, uA, vA} ρ J
      points R adj T hpoints D E hF hT H hH hK hk).tower.app (op m)) :=
  quasiIso_quotientInvariantsLimitToRepExtend.{w, max w uG, uG} (D + 2) _ H hH hK hk hS hP hR
    (isZero_exactGodementTruncatedCompactSectionsSystem_obj_X ρ J points R adj T hpoints D E hF
      hT) m
    (fun i => exactGodementTruncatedCompactRepHomology_ρ_eq_id ρ J points R adj T hpoints D E
      hF hT (htriv i))

/-- Harris (2.7) on `𝒜`: under the hypotheses of
`quasiIso_exactGodementQuotientInvariantsLimitToRepExtend`, the cohomology of `C^•_m` is the
compactly supported cohomology `H^n_c(T m)`. -/
def exactGodementQuotientInvariantsLimitHomologyIso
    (hS : ProPInvariantSubcomplexStatement.{uG, max w uG, max w uG}) {p : ℕ}
    (hP : ∀ i, IsProPSubgroup p (H i)) (hR : IsUnit (p : R)) (m : ℕ)
    (htriv : ∀ i q (g : H i),
      (SmoothRep.toRep.obj ((exactCompactDerived J R incl E q).obj (T.obj m))).ρ g =
        LinearMap.id) (n : ℕ) :
    ((exactGodementQuotientInvariantsLimit.{w, v, u, uG, uI, uA, vA} ρ J points R adj T hpoints
      D E hF hT H hH hK hk).obj m).homology n ≅
      SmoothRep.toRep.obj ((exactCompactDerived J R incl E n).obj (T.obj m)) :=
  haveI := quasiIso_exactGodementQuotientInvariantsLimitToRepExtend.{w, v, u, uG, uI, uA, vA} ρ J
    points R adj T hpoints D E hF hT H hH hK hk hS hP hR m htriv
  isoOfQuasiIsoAt ((exactGodementQuotientInvariantsLimitToRepExtend.{w, v, u, uG, uI, uA, vA} ρ J
    points R adj T hpoints D E hF hT H hH hK hk).tower.app (op m)) n ≪≫
    (extendHomologyNatIso _ n).app ((exactGodementTruncatedCompactSectionsSystem ρ J points R adj
      T hpoints D E hF hT).toRepComplexes.obj m) ≪≫
    exactGodementTruncatedCompactRepHomologyIso ρ J points R adj T hpoints D E hF hT m n

/-- Harris's `lim_m C^•_m` on `𝒜`. -/
abbrev exactGodementQuotientInvariantsInverseLimit : CochainComplex (Rep.{max w uG} R G) ℤ :=
  quotientInvariantsInverseLimit.{w, max w uG, uG} (D + 2)
    (exactGodementTruncatedCompactSectionsSystem ρ J points R adj T hpoints D E hF hT) H hH hK hk

/-- Harris's Lemma 2.8 on `𝒜`: given `ProPInvariantSubcomplexStatement` and
`FiniteCohomologyInverseLimitStatement`, if every `H i` is a normal pro-`p` subgroup, `p` is
invertible in `R`, and the compactly supported cohomology of every level of `T` is finite with
trivial action of every `H i`, then the degree-`n` cohomology of `lim_m C^•_m` is the inverse
limit over `m` of `H^n_c(T m)`. -/
def exactGodementQuotientInvariantsInverseLimitHomologyIso
    (hS : ProPInvariantSubcomplexStatement.{uG, max w uG, max w uG})
    (hS' : FiniteCohomologyInverseLimitStatement.{max w uG, max w uG} R) {p : ℕ}
    (hP : ∀ i, IsProPSubgroup p (H i)) (hR : IsUnit (p : R))
    (htriv : ∀ m i q (g : H i),
      (SmoothRep.toRep.obj ((exactCompactDerived J R incl E q).obj (T.obj m))).ρ g =
        LinearMap.id)
    (hfin : ∀ m q,
      Finite (SmoothRep.toRep.obj ((exactCompactDerived J R incl E q).obj (T.obj m))))
    (n : ℕ) :
    (exactGodementQuotientInvariantsInverseLimit.{w, v, u, uG, uI, uA, vA} ρ J points R adj T
      hpoints D E hF hT H hH hK hk).homology n ≅
      limit (T.tower ⋙ exactCompactDerived J R incl E n ⋙ SmoothRep.toRep) :=
  haveI := isIso_quotientInvariantsInverseLimitComparison.{w, max w uG, uG} (D + 2)
    (exactGodementTruncatedCompactSectionsSystem ρ J points R adj T hpoints D E hF hT) H hH hK hk
    hS hS' hP hR
    (isZero_exactGodementTruncatedCompactSectionsSystem_obj_X ρ J points R adj T hpoints D E hF
      hT)
    (fun m i => exactGodementTruncatedCompactRepHomology_ρ_eq_id ρ J points R adj T hpoints D E
      hF hT (htriv m i))
    (fun m q => finite_of_rep_iso
      (exactGodementTruncatedCompactRepHomologyIso ρ J points R adj T hpoints D E hF hT m q).symm
      (hfin m q)) n
  asIso (quotientInvariantsInverseLimitComparison.{w, max w uG, uG} (D + 2)
      (exactGodementTruncatedCompactSectionsSystem ρ J points R adj T hpoints D E hF hT) H hH hK
      hk (isZero_exactGodementTruncatedCompactSectionsSystem_obj_X ρ J points R adj T hpoints D E
        hF hT) n) ≪≫
    (exactGodementTruncatedCompactSectionsSystem ρ J points R adj T hpoints D E hF
      hT).toRepComplexes.extendLevelCohomologyLimitIso n ≪≫
    lim.mapIso (Functor.isoWhiskerLeft
      (exactGodementTruncatedCompactSectionsSystem ρ J points R adj T hpoints D E hF hT).tower
      (mapHomologicalComplexHomologyIso SmoothRep.toRep (ComplexShape.up ℕ) n)) ≪≫
    lim.mapIso (Functor.isoWhiskerRight
      (exactGodementTruncatedCompactHomologyNatIso ρ J points R adj T hpoints D E hF hT n)
      SmoothRep.toRep)

end InverseLimit

end Langlands.Cohomology.DivisibleSystem
