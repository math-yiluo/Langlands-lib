import Langlands.GroupScheme.MatrixRepresentation.GaloisCoefficients
import Langlands.GroupScheme.MultiplicativePointTopology
import Langlands.GroupScheme.Reductive.StarAction
import Langlands.GroupScheme.Rational.HighestWeightRootEndpoint
import Langlands.GroupScheme.MatrixRepresentation.GaloisCharacterSpaces
import Langlands.GroupScheme.Rational.CharacterGaloisAction

/-! # Weights of Galois twists of representations -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.MatrixRepresentation

section TransportCharacter

variable {B : Scheme.{u}} {R : CommRingCat.{u}} (b : Spec R ⟶ B) (a : Spec R ⟶ Spec R)
  (ha : a ≫ b = b) (T : CommGroupScheme B)

/-- On an affine test algebra, if the descended point is the precomposite with `Spec θ`, the
transported character has the original value with `θ` applied. -/
theorem affineUnits_transport_of_descentPoint
    (χ : characterLattice ((CommGroupScheme.baseChange b).obj T))
    (S : Type u) [CommRing S] [Algebra R S]
    (y : (algSpec R).obj (op (CommAlgCat.of R S)) ⟶ ((CommGroupScheme.baseChange b).obj T).X)
    (θ : S →+* S)
    (Θ : (Over.map a).obj ((algSpec R).obj (op (CommAlgCat.of R S))) ⟶
      (algSpec R).obj (op (CommAlgCat.of R S)))
    (hΘ : Θ.left = Spec.map (CommRingCat.ofHom θ))
    (hy : descentPoint b a ha T.toGrp _ y = Θ ≫ y) :
    (Gm.affineUnitsEquiv R (CommAlgCat.of R S)
        (y ≫ (CommGroupScheme.groupHom (characterLattice.transport b a ha T χ)).hom.hom) : S) =
      θ (Gm.affineUnitsEquiv R (CommAlgCat.of R S)
        (y ≫ (CommGroupScheme.groupHom χ).hom.hom)) := by
  have hq : Function.Injective (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom :=
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of S)).inv).1
  apply hq
  have hval : ∀ x : (algSpec R).obj (op (CommAlgCat.of R S)) ⟶ (Gm (Spec R)).X,
      (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom
          (Gm.affineUnitsEquiv R (CommAlgCat.of R S) x : S) =
        (Gm.pointsEquiv (Spec R) _ x : Γ(((algSpec R).obj (op (CommAlgCat.of R S))).left, ⊤)) := by
    intro x
    change (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom
      ((Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom (Gm.pointsEquiv (Spec R) _ x).val) = _
    exact ConcreteCategory.congr_hom (Scheme.ΓSpecIso (CommRingCat.of S)).hom_inv_id _
  rw [hval, characterLattice.transport_points, hy, Category.assoc, Gm.pointsEquiv_naturality,
    Units.coe_map]
  have hnat := ConcreteCategory.congr_hom
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom θ))
    (Gm.affineUnitsEquiv R (CommAlgCat.of R S) (y ≫ (CommGroupScheme.groupHom χ).hom.hom) : S)
  rw [← hΘ] at hnat
  rw [← hval]
  exact hnat.symm

end TransportCharacter

section Restrict

variable {B : Scheme.{u}} {R : CommRingCat.{u}} (b : Spec R ⟶ B) (a : Spec R ⟶ Spec R)
  (ha : a ≫ b = b) {G H : GroupScheme B} {n : Type} [Fintype n] [DecidableEq n]

/-- Descent of points is natural for homomorphisms over the base. -/
theorem descentPoint_comp_map (f : H ⟶ G) (T : Over (Spec R))
    (x : T ⟶ ((GroupScheme.baseChange b).obj H).X) :
    descentPoint b a ha G T (x ≫ ((GroupScheme.baseChange b).map f).hom.hom) =
      descentPoint b a ha H T x ≫ ((GroupScheme.baseChange b).map f).hom.hom := by
  apply (baseChangePointsEquiv b G ((Over.map a).obj T)).injective
  rw [baseChangePointsEquiv_descentPoint, baseChangePointsEquiv_comp, baseChangePointsEquiv_comp,
    baseChangePointsEquiv_descentPoint, Category.assoc]

/-- Restricting a transported representation along a homomorphism over the base. -/
theorem pointMatrix_transport_restrict
    (ρ : MatrixRepresentation ((GroupScheme.baseChange b).obj G) n) (f : H ⟶ G)
    (T : Over (Spec R)) (x : T ⟶ ((GroupScheme.baseChange b).obj H).X) :
    ((transport b a ha G ρ).restrict ((GroupScheme.baseChange b).map f)).pointMatrix T x =
      (ρ.restrict ((GroupScheme.baseChange b).map f)).pointMatrix ((Over.map a).obj T)
        (descentPoint b a ha H T x) := by
  rw [pointMatrix_restrict, pointMatrix_transport, descentPoint_comp_map, pointMatrix_restrict]

end Restrict

section Twist

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {G H : GroupScheme (Spec (CommRingCat.of k))}
  {n : Type} [Fintype n] [DecidableEq n]

/-- Scalar points are natural for homomorphisms defined over `k`. -/
theorem scalarPoint_comp_map (R : Type u) [CommRing R] [Algebra k R] (f : H ⟶ G)
    (g : H.affinePoints (CommAlgCat.of (CommRingCat.of k) R)) :
    scalarPoint R g ≫ ((GroupScheme.baseChange (algebraBaseMap k K)).map f).hom.hom =
      scalarPoint R (g ≫ f.hom.hom) := by
  apply (baseChangePointsEquiv (algebraBaseMap k K) G _).injective
  rw [baseChangePointsEquiv_comp]
  simp only [scalarPoint, scalarExtensionPoint, MulEquiv.apply_symm_apply, Category.assoc]

/-- Conjugating a character vector by `σ` gives a vector of the conjugate character for the
Galois twist. -/
theorem conjugate_mem_characterSpace_galoisTwist [IsAffineHom H.X.hom]
    (σ : K ≃ₐ[k] K)
    (τ : MatrixRepresentation ((GroupScheme.baseChange (algebraBaseMap k K)).obj H) n)
    (χ : rationalCharacters ((GroupScheme.baseChange (algebraBaseMap k K)).obj H))
    {v : n → K} (hv : v ∈ τ.characterSpace χ) :
    (fun i => σ (v i)) ∈ (galoisTwist σ τ).characterSpace
      (rationalCharacters.galoisRepresentation k K H σ χ) := by
  have : IsAffineHom ((GroupScheme.baseChange (algebraBaseMap k K)).obj H).X.hom :=
    inferInstanceAs (IsAffineHom (CategoryTheory.Limits.pullback.snd H.X.hom
      (algebraBaseMap k K)))
  apply (mem_characterSpace_iff_points _ _ _).mpr
  intro T x
  have h := characterSpace_pointMatrix hv
    ((Over.map (galoisBaseMap k K σ)).obj T)
    (descentPoint (algebraBaseMap k K) (galoisBaseMap k K σ)
      (galoisBaseMap_over k K σ) H T x)
  rw [galoisTwist_eq_transport, pointMatrix_transport]
  have hs (c : K) : scalarMap ((Over.map (galoisBaseMap k K σ)).obj T) c =
      scalarMap T (σ c) := scalarMap_galoisBaseMap σ T c
  simpa only [hs, rationalCharacters.characterEval_galoisRepresentation] using h

/-- Conjugating a character vector of a restriction by `σ` gives a vector of the conjugate
character for the restriction of the Galois twist. -/
theorem conjugate_mem_characterSpace_restrict_galoisTwist
    [IsAffineHom ((GroupScheme.baseChange (algebraBaseMap k K)).obj H).X.hom]
    (σ : K ≃ₐ[k] K)
    (ρ : MatrixRepresentation ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) n)
    (f : H ⟶ G)
    (χ : rationalCharacters ((GroupScheme.baseChange (algebraBaseMap k K)).obj H))
    {v : n → K}
    (hv : v ∈ (ρ.restrict ((GroupScheme.baseChange (algebraBaseMap k K)).map f)).characterSpace χ) :
    (fun i => σ (v i)) ∈
      ((galoisTwist σ ρ).restrict ((GroupScheme.baseChange (algebraBaseMap k K)).map f)).characterSpace
        (rationalCharacters.galoisRepresentation k K H σ χ) := by
  apply (mem_characterSpace_iff_points _ _ _).mpr
  intro T x
  have h := characterSpace_pointMatrix hv
    ((Over.map (galoisBaseMap k K σ)).obj T)
    (descentPoint (algebraBaseMap k K) (galoisBaseMap k K σ)
      (galoisBaseMap_over k K σ) H T x)
  rw [galoisTwist_eq_transport, pointMatrix_transport_restrict]
  have hs (c : K) : scalarMap ((Over.map (galoisBaseMap k K σ)).obj T) c =
      scalarMap T (σ c) := scalarMap_galoisBaseMap σ T c
  simpa only [hs, rationalCharacters.characterEval_galoisRepresentation] using h

/-- Twisting by `σ` and then by `σ⁻¹` does not change the universal matrix. -/
theorem universalMatrix_galoisTwist_inv [IsAffineHom G.X.hom] (σ : K ≃ₐ[k] K)
    (ρ : MatrixRepresentation ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) n) :
    universalMatrix (galoisTwist σ⁻¹ (galoisTwist σ ρ)) = universalMatrix ρ := by
  rw [universalMatrix_galoisTwist, universalMatrix_galoisTwist, Matrix.map_map]
  ext i j
  exact galoisTensor_symm_galoisTensor _ σ _

/-- Character spaces of restrictions only depend on the universal matrix. -/
theorem characterSpace_restrict_eq_of_universalMatrix_eq [IsAffineHom G.X.hom]
    {H' : GroupScheme (Spec (CommRingCat.of K))} [IsAffineHom H'.X.hom]
    (F : H' ⟶ (GroupScheme.baseChange (algebraBaseMap k K)).obj G)
    {ρ₁ ρ₂ : MatrixRepresentation ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) n}
    (h : universalMatrix ρ₁ = universalMatrix ρ₂) (χ : rationalCharacters H') :
    (ρ₁.restrict F).characterSpace χ = (ρ₂.restrict F).characterSpace χ := by
  let A := CharacterUnits.Coord H'
  let : Algebra k A := Algebra.compHom A (algebraMap k K)
  have : IsScalarTower k K A := IsScalarTower.of_algebraMap_eq' rfl
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in
  have hu : ∀ ρ : MatrixRepresentation ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) n,
      (ρ.restrict F).universalCharacterMatrix = (universalMatrix ρ).map
        (universalEval (A := A) (CharacterUnits.universalPoint H' ≫ F.hom.hom)) := by
    intro ρ
    have h1 : (ρ.affineMatrix (CharacterUnits.Coord H')
        (CharacterUnits.universalPoint H' ≫ F.hom.hom) : Matrix n n A) =
        (universalMatrix ρ).map
          (universalEval (A := A) (CharacterUnits.universalPoint H' ≫ F.hom.hom)) :=
      affineMatrix_eq_map_universalEval (A := A) ρ _
    rw [universalCharacterMatrix, affineMatrix_restrict]
    exact h1
  ext v
  rw [mem_characterSpace_iff, mem_characterSpace_iff, hu, hu, h]

end Twist

section ComapRank

variable {k K : Type u} [Field k] [Field K] [Algebra k K] {n : Type} [Fintype n] [DecidableEq n]

omit [Fintype n] [DecidableEq n] in
/-- `galoisComap τ` preserves finite rank. -/
theorem finrank_galoisComap (τ : K ≃ₐ[k] K) (V : Submodule K (n → K)) :
    Module.finrank K (galoisComap τ V) = Module.finrank K V := by
  let j : galoisComap τ V ≃+ V :=
    { toFun := fun w => ⟨fun i => τ (w.1 i), w.2⟩
      invFun := fun v => ⟨fun i => τ.symm (v.1 i), by
        rw [mem_galoisComap]
        simpa only [AlgEquiv.apply_symm_apply] using v.2⟩
      left_inv := fun w => by ext i; simp
      right_inv := fun v => by ext i; simp
      map_add' := fun w w' => by ext i; simp }
  have h := rank_eq_of_equiv_equiv (τ : K → K) j τ.bijective (fun c w => by
    ext i
    change τ (c * w.1 i) = τ c * τ (w.1 i)
    exact map_mul τ c (w.1 i))
  simp only [Module.finrank, h]

omit [Fintype n] [DecidableEq n] in
/-- `galoisComap τ` is an order isomorphism of the subspace lattice. -/
def galoisComapOrderIso (τ : K ≃ₐ[k] K) : Submodule K (n → K) ≃o Submodule K (n → K) where
  toFun := galoisComap τ
  invFun := galoisComap τ.symm
  left_inv V := by ext w; simp [mem_galoisComap]
  right_inv V := by ext w; simp [mem_galoisComap]
  map_rel_iff' {V W} := by
    constructor
    · intro h v hv
      have := h (show (fun i => τ.symm (v i)) ∈ galoisComap τ V by simpa [mem_galoisComap] using hv)
      simpa [mem_galoisComap] using this
    · intro h w hw
      exact h hw

end ComapRank

end Langlands.GroupScheme.MatrixRepresentation

namespace Langlands.GroupScheme.GaloisPinningData

open MatrixRepresentation

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (d : GaloisPinningData k K G) {n : Type} [Fintype n] [DecidableEq n]

/-- Conjugating a weight vector by `σ` gives a weight vector of the Galois twist, for the
Galois-conjugate weight. -/
theorem conjugate_mem_representationWeightSpace (σ : K ≃ₐ[k] K)
    (ρ : MatrixRepresentation ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) n)
    (mu : characterLattice d.toSplitPinning.torus) {v : n → K}
    (hv : v ∈ d.toSplitPinning.representationWeightSpace ρ mu) :
    (fun i => σ (v i)) ∈ d.toSplitPinning.representationWeightSpace (galoisTwist σ ρ)
      (characterLattice.galoisRepresentation k K d.torus σ mu) := by
  have : IsAffineHom ((GroupScheme.baseChange (algebraBaseMap k K)).obj d.torus.toGrp).X.hom :=
    d.toSplitPinning.isSplitTorus.isAffineHom
  exact conjugate_mem_characterSpace_restrict_galoisTwist σ ρ d.inclusion _ hv

/-- The weight spaces of a Galois twist are the `σ`-conjugates of the original weight spaces. -/
theorem mem_representationWeightSpace_galoisTwist_iff (σ : K ≃ₐ[k] K)
    (ρ : MatrixRepresentation ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) n)
    (mu : characterLattice d.toSplitPinning.torus) (w : n → K) :
    w ∈ d.toSplitPinning.representationWeightSpace (galoisTwist σ ρ)
        (characterLattice.galoisRepresentation k K d.torus σ mu) ↔
      (fun i => σ⁻¹ (w i)) ∈ d.toSplitPinning.representationWeightSpace ρ mu := by
  constructor
  · intro hw
    have h1 := d.conjugate_mem_representationWeightSpace σ⁻¹ (galoisTwist σ ρ) _ hw
    rw [Representation.inv_self_apply] at h1
    have : IsAffineHom d.toSplitPinning.torus.X.hom := d.toSplitPinning.isSplitTorus.isAffineHom
    have heq := characterSpace_restrict_eq_of_universalMatrix_eq d.toSplitPinning.inclusion
      (universalMatrix_galoisTwist_inv σ ρ)
      ((rationalCharacters.equivCharacterLattice d.toSplitPinning.torus).symm mu)
    change _ ∈ ((galoisTwist σ⁻¹ (galoisTwist σ ρ)).restrict
      d.toSplitPinning.inclusion).characterSpace _ at h1
    rw [heq] at h1
    exact h1
  · intro hw
    have h1 := d.conjugate_mem_representationWeightSpace σ ρ mu hw
    simpa only [AlgEquiv.aut_inv, AlgEquiv.apply_symm_apply] using h1

theorem representationWeightSpace_galoisTwist (σ : K ≃ₐ[k] K)
    (ρ : MatrixRepresentation ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) n)
    (mu : characterLattice d.toSplitPinning.torus) :
    d.toSplitPinning.representationWeightSpace (galoisTwist σ ρ)
        (characterLattice.galoisRepresentation k K d.torus σ mu) =
      galoisComap σ⁻¹ (d.toSplitPinning.representationWeightSpace ρ mu) := by
  ext w
  rw [mem_representationWeightSpace_galoisTwist_iff, mem_galoisComap]

/-- Weight multiplicities are invariant under the Weyl group. -/
theorem finrank_representationWeightSpace_weyl
    (ρ : MatrixRepresentation ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) n)
    (w : d.toSplitPinning.rootDatum.Aut) (hw : w ∈ d.toSplitPinning.rootDatum.weylGroup)
    (mu : characterLattice d.toSplitPinning.torus) :
    Module.finrank K (d.toSplitPinning.representationWeightSpace ρ (w • mu)) =
      Module.finrank K (d.toSplitPinning.representationWeightSpace ρ mu) := by
  revert mu
  induction hw using RootPairing.weylGroup.induction with
  | mem i =>
    intro mu
    rw [RootPairing.Equiv.reflection_smul]
    exact d.toSplitPinning.finrank_representationWeightSpace_root_reflection ρ mu i
  | one => intro mu; rw [one_smul]
  | mul x y _ _ hx hy => intro mu; rw [mul_smul, hx, hy]

/-- Automorphisms preserving the base preserve the positive root monoid. -/
theorem smul_mem_positiveRootMonoid (e : d.toSplitPinning.rootDatum.Aut)
    (he : e ∈ d.toSplitPinning.basedRootDatumAut) {mu : characterLattice d.toSplitPinning.torus}
    (hmu : mu ∈ d.toSplitPinning.positiveRootMonoid) :
    e • mu ∈ d.toSplitPinning.positiveRootMonoid := by
  induction hmu using AddSubmonoid.closure_induction with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    rw [← RootPairing.Equiv.root_indexEquiv_eq_smul]
    exact d.toSplitPinning.simpleRoot_mem_positiveRootMonoid ⟨e.indexEquiv a, (he a).mp a.2⟩
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy

variable [LocallyOfFiniteType G.X.hom]

theorem galoisAction_smul (σ : K ≃ₐ[k] K) (mu : characterLattice d.toSplitPinning.torus) :
    d.galoisAction σ • mu = characterLattice.galoisRepresentation k K d.torus σ mu :=
  rfl

theorem representationWeightSpace_galoisTwist_smul (σ : K ≃ₐ[k] K)
    (ρ : MatrixRepresentation ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) n)
    (mu : characterLattice d.toSplitPinning.torus) :
    d.toSplitPinning.representationWeightSpace (galoisTwist σ ρ) (d.galoisAction σ • mu) =
      galoisComap σ⁻¹ (d.toSplitPinning.representationWeightSpace ρ mu) := by
  rw [galoisAction_smul]
  exact d.representationWeightSpace_galoisTwist σ ρ mu

/-- The Galois twist of a representation of star-fixed highest weight `lam` has highest weight
`lam`. -/
theorem isHighestWeight_galoisTwist (σ : K ≃ₐ[k] K)
    {ρ : MatrixRepresentation ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) n}
    {lam : characterLattice d.toSplitPinning.torus}
    (hρ : d.toSplitPinning.IsHighestWeight ρ lam) (hfix : (d.starAction σ).val • lam = lam) :
    d.toSplitPinning.IsHighestWeight (galoisTwist σ ρ) lam := by
  obtain ⟨w, hw⟩ := d.exists_weyl_mul_galoisAction_eq_starAction σ
  have hstar : ∀ mu : characterLattice d.toSplitPinning.torus,
      (d.starAction σ).val • mu = w.val • (d.galoisAction σ • mu) := by
    intro mu
    rw [← hw, mul_smul]
  have hne : ∀ (ρ' : MatrixRepresentation ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) n)
      (mu : characterLattice d.toSplitPinning.torus),
      d.toSplitPinning.representationWeightSpace ρ' mu ≠ ⊥ ↔
        Module.finrank K (d.toSplitPinning.representationWeightSpace ρ' mu) ≠ 0 := by
    intro ρ' mu
    rw [Ne, Ne, Submodule.finrank_eq_zero]
  refine ⟨hρ.1.galoisTwist σ, ?_, ?_, ?_⟩
  · rw [eq_top_iff]
    calc (⊤ : Submodule K (n → K))
        = galoisComapOrderIso σ⁻¹ (⨆ mu, d.toSplitPinning.representationWeightSpace ρ mu) := by
          rw [hρ.2.1, OrderIso.map_top]
      _ = ⨆ mu, galoisComap σ⁻¹ (d.toSplitPinning.representationWeightSpace ρ mu) :=
          OrderIso.map_iSup _ _
      _ ≤ ⨆ nu, d.toSplitPinning.representationWeightSpace (galoisTwist σ ρ) nu := by
          refine iSup_le fun mu => ?_
          rw [← representationWeightSpace_galoisTwist_smul]
          exact le_iSup (fun nu => d.toSplitPinning.representationWeightSpace (galoisTwist σ ρ) nu)
            _
  · have hl : lam = w.val • (d.galoisAction σ • lam) := by
      rw [← hstar, hfix]
    rw [hl, d.finrank_representationWeightSpace_weyl _ w.val w.2,
      representationWeightSpace_galoisTwist_smul, finrank_galoisComap, hρ.2.2.1]
  · intro mu hmu
    let nu : characterLattice d.toSplitPinning.torus := (d.galoisAction σ)⁻¹ • (w.val⁻¹ • mu)
    have hgnu : d.galoisAction σ • nu = w.val⁻¹ • mu := smul_inv_smul _ _
    have hnu : d.toSplitPinning.representationWeightSpace ρ nu ≠ ⊥ := by
      rw [hne] at hmu ⊢
      have h1 := d.finrank_representationWeightSpace_weyl (galoisTwist σ ρ) w.val⁻¹
        (inv_mem w.2) mu
      rw [← hgnu, representationWeightSpace_galoisTwist_smul, finrank_galoisComap] at h1
      rw [h1]
      exact hmu
    have hle := hρ.2.2.2 nu hnu
    have h2 := d.smul_mem_positiveRootMonoid (d.starAction σ).val (d.starAction σ).2 hle
    rw [smul_sub, hfix, hstar nu, hgnu, smul_inv_smul] at h2
    exact h2

end Langlands.GroupScheme.GaloisPinningData
