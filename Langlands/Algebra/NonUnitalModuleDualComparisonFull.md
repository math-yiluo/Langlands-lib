# Full-dual comparison under double-opposite transport

Worker 1149 completes and extends Worker 6's feasibility construction. This is a
derived internal comparison supporting the two dual functors of Renard I.4.1,
printed pages 22–23 / PDF pages 28–29. The governing source is David Renard,
*Représentations des groupes réductifs p-adiques*, French version 9 July 2026,
registered as `renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The original nonunital conventions are on printed pages 5–7 / PDF pages 11–13;
the canonical complex scalars are I.2.1, printed page 14 / PDF page 20.
The registered `renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
PDF pages 1–2, changes no construction here; its nonzero-vector correction
concerns the later injectivity argument. The 2026 edition governs.

All declarations are in `Langlands.Algebra.NonUnitalModuleDualComparison`.
For an original nondegenerate double-opposite action on the specified additive
carrier M, `rawCanonicalModule` names the entire recovered complex module for
`hA.op.op`; `transportedCanonicalModule` names the entire recovered module after
`fromDoubleOppositeAction`. `transportedCanonicalModule_eq_raw` and
`canonicalModule_names` prove equality of these complete structures. The proof
installs the raw canonical module and scalar tower, transports that tower to A,
and uses uniqueness of a compatible recovered module. No complex module on M
is assumed.

`fullComparison` is a complex-linear equivalence between the two actual full
duals, with the precise recovered modules used in their definitions. Both
directions retain the entire underlying function, as `fullComparison_coe` and
`fullComparison_symm_coe` state. Linearity in each direction follows from the
complete scalar equality. Additive, scalar and inverse laws use functional
extensionality.

`fullComparisonHom` and `fullComparisonInvHom` bundle these same maps as
original A-opposite intertwiners. Their signatures explicitly install the raw
triple-opposite full-dual action, transport it twice back to A-opposite, and
install the target full-dual action. The additive-map agreements are
definitional. `fullComparison_inverse_left` and
`fullComparison_inverse_right` identify the entire composite intertwiners with
the appropriate identities. Intertwining reduces at each m to the same
original double-opposite action.

The complete unapplied equivalence and original-map interfaces are explicitly
assigned with independent algebra and carrier universes. No finite dimension,
nontriviality, unit law, faithful action, anti-involution or comparison witness
is added. Zero carriers and zero algebras remain included. This pair constructs
no evaluation and proves no injection, exactness or reflexivity. The separate
subtype comparison and actual right categorical composite use these interfaces.
