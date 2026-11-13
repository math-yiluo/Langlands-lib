# Existence of z-extensions

`Langlands.GroupScheme.ZExtensionExistenceStatement` is the proposition that
every connected reductive group scheme over every field admits a z-extension,
with the exact meaning of `ZExtension` in the companion definition module.
It is an existence statement, not a proof and not an additional hypothesis
on the later local-field Kottwitz statements.

The source is Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023),
Construction 11.4.1, printed p. 428 (PDF p. 459), source ID
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
Section 11.3 explicitly allows every field and §11.4 constructs the
z-extension over that field before §11.5 specializes to the maximal
unramified field. The 1 November 2024 corrections do not alter this item.

In the printed construction one embeds the finite kernel of the product
of the connected center and the simply connected derived cover into an
induced torus, then takes a pushout. The present proposition records the
existence of the resulting actual fppf exact sequence with induced central
torus kernel and connected reductive source with simply connected derived
group. No separability, perfectness, characteristic-zero, split or
quasi-split assumption is imposed on the ground field or group. The
proof, including the pushout construction, remains a separate obligation.
